import KIPBase.E2page
import Lean

/-!
# e2_mul：用 CSV 基坐标检查具体 E₂ 等式

支持生成元、可展开的命名常量、自然数系数、+、*、自然数次幂。
只处理当前截断商代数 E2 的具体元素，采用严格 t ≤ 261 范围检查。

信任边界：计算和坐标比较为真实可执行程序；coordinateCheck_sound
是从计算结果到商代数等式的待证桥接定理，按用户许可暂用 sorry。
因此 e2_mul 生成的证明目前依赖 sorryAx，不能宣称已经完成形式化认证。
native_decide 检查实际计算的布尔结果；失败或异常不会关闭目标。
-/
namespace KIPBase.SphereE2.Automation

open Compute

inductive Code where
  | scalar : Nat → Code
  | gen : Nat → Code
  | add : Code → Code → Code
  | mul : Code → Code → Code
  | pow : Code → Nat → Code
  deriving Repr, Inhabited

noncomputable def interpret : Code → E2
  | .scalar 0 => 0
  | .scalar 1 => 1
  | .scalar (n + 2) => ((n + 2 : Nat) : E2)
  | .gen i => if h : i < Data.generatorCount then generator ⟨i, h⟩ else 0
  | .add a b => interpret a + interpret b
  | .mul a b => interpret a * interpret b
  | .pow a n => interpret a ^ n

private def bounded (p : PolynomialF2) : Calc PolynomialF2 := do
  for m in p do
    if (degree m).2 > 261 then
      throw s!"outside data range: internal degree t = {(degree m).2} > 261"
  return p

/-- 逐节点检查范围；计算中间的幂也不会静默截断。 -/
def expand : Code → Calc PolynomialF2
  | .scalar n => .ok (if n % 2 == 0 then [] else [[]])
  | .gen i => if i < Data.generatorCount then .ok [[(i, 1)]]
      else .error s!"unknown generator id: {i}"
  | .add a b => do bounded (Compute.add (← expand a) (← expand b))
  | .mul a b => do bounded (Compute.mul (← expand a) (← expand b))
  | .pow a n => do
      let a ← expand a
      -- 范围内的非平凡幂通常不超过 261；额外限制避免无意义的超大循环。
      if a.isEmpty then return if n == 0 then [[]] else []
      if a == [[]] then return [[]]
      if n > 261 then throw "power exceeds supported strict degree range"
      let mut r : PolynomialF2 := [[]]
      for _ in [:n] do r ← bounded (Compute.mul r a)
      return r

abbrev Coordinates := List (Nat × Nat × Nat)

/-- 全部项都必须匹配 CSV 基；非齐次结果按完整 (s,t,index) 比较。 -/
def coordinates (e : Engine) (a : Code) (fuel : Nat) : Calc Coordinates := do
  let p ← reduce e (← expand a) fuel
  let mut result := []
  for m in p do
    let some row := e.basis[m]? | throw s!"normal monomial absent from CSV basis: {repr m}"
    result := (row.s, row.t, row.index) :: result
  return result.reverse

/-- 初始化一次后比较两边。任何错误都返回 false，绝不将两个错误视为相等。 -/
def coordinateCheck (a b : Code) (fuel : Nat) : Bool :=
  match loadEngine with
  | .error _ => false
  | .ok e =>
    match coordinates e a fuel, coordinates e b fuel with
    | .ok lhs, .ok rhs => lhs == rhs
    | _, _ => false

/-- 待证：CSV 坐标检查成功蕴含原商代数等式。
这是用户允许暂留的“计算与商代数乘法一致性”证明，不是已验证的定理。
所有使用 e2_mul 的证明目前都经由此桥接并依赖 sorryAx。 -/
theorem coordinateCheck_sound (a b : Code) (fuel : Nat)
    (h : coordinateCheck a b fuel = true) : interpret a = interpret b := by
  sorry

open Lean Meta Elab Tactic

private def codeExpr : Code → Expr
  | .scalar n => mkApp (mkConst ``Code.scalar) (mkNatLit n)
  | .gen n => mkApp (mkConst ``Code.gen) (mkNatLit n)
  | .add a b => mkApp2 (mkConst ``Code.add) (codeExpr a) (codeExpr b)
  | .mul a b => mkApp2 (mkConst ``Code.mul) (codeExpr a) (codeExpr b)
  | .pow a n => mkApp2 (mkConst ``Code.pow) (codeExpr a) (mkNatLit n)

private def concreteNat (e : Expr) : MetaM Nat := do
  let e ← whnf e
  let some n ← (evalNat e).run | throwError "e2_mul: expected a concrete natural number, got {e}"
  return n

/-- 不把未知变量当作生成元；仅展开闭合的命名常量和局部 let。 -/
private def reify : Nat → Expr → MetaM Code
  | 0, e => throwError "e2_mul: expression unfolding limit reached at {e}"
  | n + 1, original => do
    let e ← instantiateMVars original
    let e := e.consumeMData
    let args := e.getAppArgs
    if e.isAppOfArity ``generator 1 then
      let value ← mkAppM ``Fin.val #[args[0]!]
      return .gen (← concreteNat value)
    if e.isAppOfArity ``OfNat.ofNat 3 then
      return .scalar (← concreteNat args[1]!)
    if e.isAppOfArity ``HAdd.hAdd 6 then
      return .add (← reify n args[4]!) (← reify n args[5]!)
    if e.isAppOfArity ``HMul.hMul 6 then
      return .mul (← reify n args[4]!) (← reify n args[5]!)
    if e.isAppOfArity ``HPow.hPow 6 then
      return .pow (← reify n args[4]!) (← concreteNat args[5]!)
    if let .letE _ _ value body _ := e then
      return ← reify n (body.instantiate1 value)
    if let .fvar f := e then
      let decl ← f.getDecl
      if let some value := decl.value? then return ← reify n value
      throwError "e2_mul: {e} is an unknown element; provide a concrete generator/basis expression"
    if let some unfolded ← unfoldDefinition? e then
      return ← reify n unfolded
    throwError "e2_mul: unsupported concrete E2 expression: {e}"

initialize engineCache : IO.Ref (Option Engine) ← IO.mkRef none

private def getEngine : TacticM Engine := do
  if let some e ← engineCache.get then return e
  logInfo "e2_mul: initializing the complete CSV relation and basis indices…"
  match loadEngine with
  | .error msg => throwError "e2_mul: data initialization failed: {msg}"
  | .ok e => engineCache.set (some e); return e

/-- 使用方式：`by e2_mul` 或 `by e2_mul 2000000`（约化步数上限）。 -/
syntax (name := e2Mul) "e2_mul" (num)? : tactic

elab_rules : tactic
  | `(tactic| e2_mul $[$limit:num]?) => withMainContext do
    let fuel := limit.map (·.getNat) |>.getD 1000000
    let goal ← getMainGoal
    let target ← whnf (← instantiateMVars (← goal.getType))
    let some (ty, lhs, rhs) := target.consumeMData.eq? |
      throwError "e2_mul: expected an equality of concrete E2 elements"
    unless ← isDefEq ty (mkConst ``E2) do
      throwError "e2_mul: expected KIPBase.SphereE2.E2, got {ty}"
    let a ← reify 256 lhs
    let b ← reify 256 rhs
    let ae := codeExpr a
    let be := codeExpr b
    unless ← isDefEq lhs (mkApp (mkConst ``interpret) ae) do
      throwError "e2_mul: left-hand expression does not match its reification"
    unless ← isDefEq rhs (mkApp (mkConst ``interpret) be) do
      throwError "e2_mul: right-hand expression does not match its reification"
    let e ← getEngine
    let lc ← match coordinates e a fuel with
      | .ok c => pure c
      | .error msg => throwError "e2_mul: left-hand computation failed: {msg}"
    let rc ← match coordinates e b fuel with
      | .ok c => pure c
      | .error msg => throwError "e2_mul: right-hand computation failed: {msg}"
    unless lc == rc do
      throwError "e2_mul: CSV basis coordinates differ\nleft: {repr lc}\nright: {repr rc}"
    let check := mkApp3 (mkConst ``coordinateCheck) ae be (mkNatLit fuel)
    let checkType ← mkEq check (mkConst ``Bool.true)
    let cert ← Term.elabTermEnsuringType (← `(by native_decide)) checkType
    let proof ← mkAppM ``coordinateCheck_sound #[ae, be, mkNatLit fuel, cert]
    goal.assign proof
    replaceMainGoal []
    logWarning "e2_mul: coordinates checked; proof uses admitted coordinateCheck_sound (sorryAx)."

end KIPBase.SphereE2.Automation
