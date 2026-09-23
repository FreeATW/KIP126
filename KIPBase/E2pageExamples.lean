import KIPBase.E2pageCompute

/-!
可执行示例及回归检查。只初始化一次完整数据索引。
可用 `lake env lean KIPBase/E2pageExamples.lean` 运行下面的 #eval。
无 sorry；这些是运行时检查，不是 Ext 正确性的形式化证明。
-/
namespace KIPBase.SphereE2.Compute

private def isFailure {α : Type} : Calc α → Bool
  | .error _ => true
  | .ok _ => false

private def require (ok : Bool) (message : String) : Calc Unit :=
  if ok then .ok () else .error message

private def expectProduct (e : Engine) (a b expected : String) : Calc Unit := do
  let r ← e.multiplyStrings a b
  let p ← parsePolynomial expected
  require (r.normalForm == p) s!"unexpected product: {a} times {b}"

/-- 初始化后执行基础代数、输入边界和两条约化路径的回归检查。 -/
def regression (e : Engine) : Calc Unit := do
  expectProduct e "0,1" "1,1" "0"
  expectProduct e "1,1" "2,1" "0"
  expectProduct e "0,1" "0,1" "0,2"
  expectProduct e "1,2" "1,1" "0,2,2,1"
  expectProduct e "2,2" "2,1" "1,2,3,1"
  expectProduct e "0,1;1,1" "1,1" "1,2"
  expectProduct e "0,1;0,1" "2,1" "0"
  expectProduct e "" "0,1;1,1" "0,1;1,1"
  expectProduct e "1,1,0,1" "" "0"
  expectProduct e "0,1,0,1" "" "0,2"
  expectProduct e "1,3" "0,1" "0"
  expectProduct e "0,2,2,1" "0,1" "0"
  expectProduct e "0" "" "0"
  expectProduct e "0,0" "1,1" "1,1"
  let r ← e.multiplyStrings "1,2" "1,1"
  require (r.coordinates.map (fun c => (c.s, c.t, c.index)) == #[(3,6,0)])
    "wrong basis coordinate for h1 cubed"
  let r ← e.multiplyBasis #[(2,4,0)] #[(1,2,0)]
  require (r.normalForm == (← parsePolynomial "0,2,2,1")) "basis-input mismatch"
  for bad in ["2914,1", "1", "x,1", "1,-1"] do
    require (isFailure (e.multiplyStrings bad "")) s!"accepted invalid input {bad}"
  require (isFailure (e.multiplyBasis #[(1,2,99)] #[(0,0,0)])) "accepted unknown basis index"
  require (isFailure (e.multiplyStrings "0,261" "0,1")) "accepted out-of-range product"
  require (isFailure (e.multiplyStrings "0,262" "")) "accepted out-of-range input"
  let truncated ← e.multiplyTruncated "0,261" "0,1"
  require truncated.normalForm.isEmpty "wrong truncation"
  require (isFailure (e.multiplyStrings "1,2" "1,1" 0)) "accepted exhausted fuel"
  -- Commutativity and associativity on all triples among h0, h1, h2, h3.
  for i in [:4] do
    for j in [:4] do
      let a ← parsePolynomial s!"{i},1"
      let b ← parsePolynomial s!"{j},1"
      let ab ← reduce e (mul a b)
      let ba ← reduce e (mul b a)
      require (ab == ba) "commutativity regression"
      for k in [:4] do
        let c ← parsePolynomial s!"{k},1"
        let bc ← reduce e (mul b c)
        let left ← reduce e (mul ab c)
        let right ← reduce e (mul a bc)
        require (left == right) "associativity regression"

/-- 一次加载所有关系和基，展示乘法并运行回归检查。 -/
def demo : IO Unit := do
  let start ← IO.monoMsNow
  let e ← match loadEngine with
    | .ok e => pure e
    | .error msg => throw (IO.userError msg)
  IO.println s!"Loaded {e.rules.size} rules and {e.basis.size} basis monomials."
  for (a, b) in [("0,1", "1,1"), ("0,1", "0,1"),
      ("1,2", "1,1"), ("2,2", "2,1"), ("0,1;1,1", "1,1")] do
    match e.multiplyStrings a b with
    | .ok r => IO.println s!"{a} times {b}: {displayResult r}"
    | .error msg => throw (IO.userError msg)
  match regression e with
  | .ok () => IO.println "All regression checks passed."
  | .error msg => throw (IO.userError msg)
  IO.println s!"Elapsed: {(← IO.monoMsNow) - start} ms"

#eval demo

end KIPBase.SphereE2.Compute
