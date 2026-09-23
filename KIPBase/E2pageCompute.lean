import Std
import KIPBase.E2pageData

/-!
可执行的球谱 E₂ Gröbner 约化器（v126.3.cw49，内部次数 ≤ 261）。
复现同版 source code.zip 中 alg::GE / alg2::Mon 的比较和首项约化。
使用导出的 Gröbner 规则；不重新运行 Buchberger，也不声称已证明其完备性。
本模块无 sorry、axiom、noncomputable。错误输入、超范围、燃料耗尽、
无法匹配 CSV 基的余项均显式报错。初始化一次 Engine 后可重复查询。
空单项式字符串表示 1，整个多项式字符串 "0" 表示零。
-/
namespace KIPBase.SphereE2.Compute

abbrev Monomial := List (Nat × Nat)
abbrev PolynomialF2 := List Monomial
abbrev Calc := Except String

/-- 与原程序相同的稀疏单项式排序；排在最前面的项用于约化。 -/
def monLT : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | (i, a) :: xs, (j, b) :: ys =>
    if i != j then i > j else if a != b then a < b else monLT xs ys

private def insertPower (i a : Nat) : Monomial → Monomial
  | [] => if a == 0 then [] else [(i, a)]
  | (j, b) :: rest =>
    if a == 0 then (j, b) :: rest
    else if i < j then (i, a) :: (j, b) :: rest
    else if i == j then (j, a + b) :: rest
    else (j, b) :: insertPower i a rest

def mulMon (a b : Monomial) : Monomial :=
  b.foldl (fun m (i, e) => insertPower i e m) a

/-- 返回 m / divisor；不能整除则返回 none。 -/
def divideMon : Monomial → Monomial → Option Monomial
  | m, [] => some m
  | [], _ :: _ => none
  | (i, a) :: ms, (j, b) :: ds =>
    if i < j then ((i, a) :: ·) <$> divideMon ms ((j, b) :: ds)
    else if i > j || a < b then none
    else do
      let rest ← divideMon ms ds
      return if a == b then rest else (i, a - b) :: rest

/-- F₂ 加法：相同单项式出现偶数次就抵消。 -/
def normalize (p : PolynomialF2) : PolynomialF2 :=
  let sorted := p.mergeSort (fun a b => !monLT b a)
  (sorted.foldl (fun acc m =>
    if acc.head? == some m then acc.tail else m :: acc) []).reverse

def add (p q : PolynomialF2) : PolynomialF2 := normalize (p ++ q)
def mul (p q : PolynomialF2) : PolynomialF2 :=
  normalize (p.flatMap fun m => q.map (mulMon m))

private def readNat (s : String) : Calc Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"invalid natural number: {s}"

private def parsePowers : List String → Calc Monomial
  | [] => .ok []
  | [_] => .error "monomial must contain generator/exponent pairs"
  | i :: a :: rest => do
    let i ← readNat i
    let a ← readNat a
    if i ≥ Data.generatorCount then throw s!"unknown generator id: {i}"
    return insertPower i a (← parsePowers rest)

def parseMonomial (s : String) : Calc Monomial :=
  if s == "" then .ok [] else parsePowers (s.splitOn ",")

def parsePolynomial (s : String) : Calc PolynomialF2 := do
  if s == "0" then return []
  return normalize (← (s.splitOn ";").mapM parseMonomial)

def degree (m : Monomial) : Nat × Nat :=
  m.foldl (fun (s, t) (i, a) =>
    let row := Data.generators[i]!
    (s + a * row.2.1, t + a * row.2.2)) (0, 0)

private def checkRange (p : PolynomialF2) : Calc Unit := do
  for m in p do
    if (degree m).2 > 261 then
      throw s!"outside data range: internal degree t = {(degree m).2} > 261"

structure Rule where
  lead : Monomial
  tail : PolynomialF2
  deriving Repr, Inhabited

structure BasisTerm where
  s : Nat
  t : Nat
  index : Nat
  monomial : Monomial
  deriving Repr, BEq, Inhabited

structure Result where
  normalForm : PolynomialF2
  coordinates : Array BasisTerm
  deriving Repr, BEq, Inhabited

structure Engine where
  rules : Array Rule
  /-- 按首项的最小、最大生成元编号索引，避免扫描数千条无关规则。 -/
  buckets : Std.HashMap (Nat × Nat) (Array Nat)
  basis : Std.HashMap Monomial BasisTerm
  byCoordinate : Std.HashMap (Nat × Nat × Nat) Monomial

private def findRule (e : Engine) (m : Monomial) : Option (Nat × Monomial) := Id.run do
  for (i, _) in m do
    for (j, _) in m do
      if i ≤ j then
        for r in e.buckets[(i, j)]?.getD #[] do
          if let some q := divideMon m e.rules[r]!.lead then
            return some (r, q)
  return none

/-- 消耗一个 fuel 处理一个首项（约化或移入余式）。不会返回未完成的余式。 -/
def reduce (e : Engine) (p : PolynomialF2) (fuel : Nat := 1000000) : Calc PolynomialF2 :=
  go fuel (normalize p) []
where
  go : Nat → PolynomialF2 → PolynomialF2 → Calc PolynomialF2
    | _, [], remainder => .ok (normalize remainder)
    | 0, _ :: _, _ => .error "reduction fuel exhausted; no normal form returned"
    | n + 1, m :: rest, remainder =>
      match findRule e m with
      | none => go n rest (m :: remainder)
      | some (r, q) => go n (add rest (e.rules[r]!.tail.map (mulMon q))) remainder

/-- 解析、检查全部关系，建立首项整除索引及 CSV 基索引。 -/
def loadEngine : Calc Engine := do
  let mut e : Engine := {
    rules := #[]
    buckets := {}
    basis := {}
    byCoordinate := {} }
  for code in Data.relations do
    let original ← (code.splitOn ";").mapM parseMonomial
    let p := normalize original
    if p != original then throw s!"relation is not in archived canonical order: {code}"
    let lead :: tail := p | throw "zero relation in CSV"
    let (i, _) :: _ := lead | throw "unit leading term in CSV"
    let d := degree lead
    if d.2 > 261 then throw "relation exceeds degree bound"
    for m in tail do
      if degree m != d then throw "inhomogeneous CSV relation"
      if !monLT lead m then throw "relation tail does not advance the archived order"
    let r := e.rules.size
    let key := (i, lead.getLast!.1)
    let bucket := e.buckets[key]?.getD #[]
    e := { e with
      rules := e.rules.push ⟨lead, tail⟩
      buckets := e.buckets.insert key (bucket.push r) }
  if e.rules.size != Data.relationCount then throw "relation count mismatch"
  for chunk in Data.basisChunks do
    for line in chunk.splitOn "\n" do
      let [s, t, index, code] := line.splitOn "|" | throw "malformed basis row"
      let s ← readNat s
      let t ← readNat t
      let index ← readNat index
      let m ← parseMonomial code
      if degree m != (s, t) || t > 261 then throw "basis degree mismatch"
      if e.basis.contains m || e.byCoordinate.contains (s, t, index) then
        throw "duplicate basis monomial or coordinate"
      if (findRule e m).isSome then throw "CSV basis monomial is reducible"
      e := { e with
        basis := e.basis.insert m ⟨s, t, index, m⟩
        byCoordinate := e.byCoordinate.insert (s, t, index) m }
  if e.basis.size != Data.basisCount then throw "basis count mismatch"
  return e

private def toResult (e : Engine) (p : PolynomialF2) : Calc Result := do
  let mut cs := #[]
  for m in p do
    let some row := e.basis[m]? | throw s!"normal monomial absent from CSV basis: {repr m}"
    cs := cs.push row
  return ⟨p, cs⟩

/-- 默认严格范围接口；任意输入项或乘积项超出 t ≤ 261 时报告错误。 -/
def Engine.multiplyStrings (e : Engine) (a b : String)
    (fuel : Nat := 1000000) : Calc Result := do
  let a ← parsePolynomial a
  let b ← parsePolynomial b
  checkRange a
  checkRange b
  let p := mul a b
  checkRange p
  toResult e (← reduce e p fuel)

/-- 明确选择截断代数语义：删除乘积中 t > 261 的项。 -/
def Engine.multiplyTruncated (e : Engine) (a b : String)
    (fuel : Nat := 1000000) : Calc Result := do
  let a ← parsePolynomial a
  let b ← parsePolynomial b
  let p := (mul a b).filter (fun m => (degree m).2 ≤ 261)
  toResult e (← reduce e p fuel)

/-- 基坐标输入；数组表示各基向量之和，重复向量相消。 -/
def Engine.multiplyBasis (e : Engine)
    (a b : Array (Nat × Nat × Nat)) (fuel : Nat := 1000000) : Calc Result := do
  let decode := fun (coords : Array (Nat × Nat × Nat)) => coords.toList.mapM fun key =>
    match e.byCoordinate[key]? with
    | some m => .ok m
    | none => .error s!"unknown basis coordinate: {repr key}"
  let p := mul (← decode a) (← decode b)
  checkRange p
  toResult e (← reduce e p fuel)

def displayMonomial (m : Monomial) : String :=
  if m.isEmpty then "1" else
    String.intercalate " * " (m.map fun (i, a) =>
      let name := (Data.generators[i]!).1
      let name := if name == "[NULL]" || name == "" then s!"x_{i}" else name
      if a == 1 then name else s!"({name})^{a}")

def displayResult (r : Result) : String :=
  if r.normalForm.isEmpty then "0; basis coordinates: []" else
    String.intercalate " + " (r.normalForm.map displayMonomial) ++ "\n  " ++
      String.intercalate "; " (r.coordinates.toList.map fun c =>
        s!"(s,t)=({c.s},{c.t}), basis index={c.index}")

end KIPBase.SphereE2.Compute
