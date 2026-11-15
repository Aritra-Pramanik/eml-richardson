module

public import Mathlib

/-!
# EML trees: zero-equivalence and root existence are undecidable (statements)

The binary operator `eml(x, y) = exp x − ln y` (Odrzywołek, arXiv:2603.21852), together
with the constant 1 and a variable x, generates the elementary functions. An *EML tree*
is a binary tree built from `1`, `x` and `eml`.

This file states, assuming **Richardson's theorem** as a hypothesis:

* `compiler_exists`: there is a computable map from Richardson expressions to EML trees
  that preserves the value at every real `x`, and whose trees never apply `log` to `0`
  at any real input.
* `eml_zero_undecidable` / `eml_root_undecidable`: deciding whether an EML tree is
  identically zero on ℝ, or has a real root, is not computable.
* `…_partial` and `…_any`: the same two statements hold when `log 0` is undefined
  (partial semantics `evalO`) or is given any fixed value `c` (semantics `evalJ c`).
  So the results do not depend on Mathlib's convention `Complex.log 0 = 0`.

Richardson's theorem (D. Richardson, 1968) says that it is undecidable whether an
expression built from rationals, π, ln 2, x, +, ×, sin, exp and |·| is identically zero
on ℝ, and also whether it has a real root. Here it is **not proved**; it appears as an
explicit hypothesis of each undecidability theorem, stated for the Gödel numbering of
Richardson expressions fixed below. Computability (`Computable`, `ComputablePred`) is
Mathlib's notion for types with a `Primcodable` structure, which the explicit bijections
`eE` and `eR` with ℕ provide.

EML trees are evaluated over ℂ with the principal branch of `Complex.log`. Complex values
are needed because signed arithmetic, π and sin pass through logarithms of negative
numbers and through `i`.
-/

@[expose] public section

namespace EmlRichardson

/-! ## Richardson expressions and EML trees -/

/-- Richardson's basis: rationals, π, ln 2, the variable x, +, ×, sin, exp, |·|.
    `rat p q d` denotes the rational (p − q)/(d + 1); every rational arises this way. -/
inductive RExpr where
  | rat (p q d : ℕ)
  | pi
  | ln2
  | var
  | add (a b : RExpr)
  | mul (a b : RExpr)
  | sin (a : RExpr)
  | exp (a : RExpr)
  | abs (a : RExpr)
  deriving DecidableEq, Repr

/-- Real-valued semantics of a Richardson expression at `x`. -/
noncomputable def RExpr.eval (x : ℝ) : RExpr → ℝ
  | .rat p q d => ((p : ℝ) - q) / (d + 1)
  | .pi      => Real.pi
  | .ln2     => Real.log 2
  | .var     => x
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x
  | .sin a   => Real.sin (a.eval x)
  | .exp a   => Real.exp (a.eval x)
  | .abs a   => |a.eval x|

/-- One-variable EML trees: S → 1 | x | eml(S, S). -/
inductive EmlExpr where
  | one
  | var
  | app (l r : EmlExpr)
  deriving DecidableEq, Repr

/-- The EML operator over ℂ with Mathlib's principal `Complex.log`
    (which is total, with `Complex.log 0 = 0`). -/
noncomputable def ceml (x y : ℂ) : ℂ := Complex.exp x - Complex.log y

/-- Complex semantics of an EML tree at `x`. -/
noncomputable def EmlExpr.evalC (x : ℂ) : EmlExpr → ℂ
  | .one     => 1
  | .var     => x
  | .app l r => ceml (l.evalC x) (r.evalC x)

/-! ## Gödel numberings

Explicit bijections with ℕ. They fix the `Primcodable` structures, and hence the meaning
of `Computable` and `ComputablePred`, in the statements below. The four inverse laws are
left as `sorry` here; `Solution.lean` proves them, and Comparator checks those proofs. -/

/-- one ↦ 0, x ↦ 1, eml(l, r) ↦ ⟨l, r⟩ + 2, with Mathlib's pairing `Nat.pair`. -/
def encE : EmlExpr → ℕ
  | .one => 0
  | .var => 1
  | .app l r => Nat.pair (encE l) (encE r) + 2

/-- Inverse of `encE`. -/
def decE : ℕ → EmlExpr
  | 0 => .one
  | 1 => .var
  | n + 2 => .app (decE n.unpair.1) (decE n.unpair.2)
termination_by n => n
decreasing_by
  all_goals (have := Nat.unpair_left_le n; have := Nat.unpair_right_le n; omega)

theorem decE_encE : ∀ t, decE (encE t) = t := by
  sorry

theorem encE_decE : ∀ n, encE (decE n) = n := by
  sorry

/-- The Gödel numbering of EML trees. -/
def eE : EmlExpr ≃ ℕ := ⟨encE, decE, decE_encE, encE_decE⟩

instance : Primcodable EmlExpr := Primcodable.ofEquiv ℕ eE

/-- π ↦ 0, ln 2 ↦ 1, x ↦ 2; otherwise 6k + tag + 3 with the children packed in k. -/
def encR : RExpr → ℕ
  | .pi => 0
  | .ln2 => 1
  | .var => 2
  | .rat p q d => 6 * Nat.pair p (Nat.pair q d) + 3
  | .add a b => 6 * Nat.pair (encR a) (encR b) + 4
  | .mul a b => 6 * Nat.pair (encR a) (encR b) + 5
  | .sin a => 6 * encR a + 6
  | .exp a => 6 * encR a + 7
  | .abs a => 6 * encR a + 8

/-- Inverse of `encR`. -/
def decR : ℕ → RExpr
  | 0 => .pi
  | 1 => .ln2
  | 2 => .var
  | n + 3 =>
    if n % 6 = 0 then .rat (n / 6).unpair.1 (n / 6).unpair.2.unpair.1 (n / 6).unpair.2.unpair.2
    else if n % 6 = 1 then .add (decR (n / 6).unpair.1) (decR (n / 6).unpair.2)
    else if n % 6 = 2 then .mul (decR (n / 6).unpair.1) (decR (n / 6).unpair.2)
    else if n % 6 = 3 then .sin (decR (n / 6))
    else if n % 6 = 4 then .exp (decR (n / 6))
    else .abs (decR (n / 6))
termination_by n => n
decreasing_by
  all_goals (have := Nat.unpair_left_le (n / 6); have := Nat.unpair_right_le (n / 6); have := Nat.div_le_self n 6; omega)

theorem decR_encR : ∀ e, decR (encR e) = e := by
  sorry

theorem encR_decR : ∀ n, encR (decR n) = n := by
  sorry

/-- The Gödel numbering of Richardson expressions. -/
def eR : RExpr ≃ ℕ := ⟨encR, decR, decR_encR, encR_decR⟩

instance : Primcodable RExpr := Primcodable.ofEquiv ℕ eR

/-! ## No log of 0, and conventions for log 0 -/

/-- `Safe x t`: every `log` node of `t` (the right child of every `eml` node) receives a
    nonzero argument when `t` is evaluated at `x`. -/
def Safe (x : ℂ) : EmlExpr → Prop
  | .one => True
  | .var => True
  | .app l r => Safe x l ∧ Safe x r ∧ r.evalC x ≠ 0

open Classical in
/-- Partial semantics: undefined (`none`) as soon as some `log` receives 0. -/
noncomputable def EmlExpr.evalO (x : ℂ) : EmlExpr → Option ℂ
  | .one => some 1
  | .var => some x
  | .app l r =>
    match l.evalO x, r.evalO x with
    | some u, some v => if v = 0 then none else some (Complex.exp u - Complex.log v)
    | _, _ => none

open Classical in
/-- Semantics in which `log 0` is the arbitrary fixed value `c`. -/
noncomputable def EmlExpr.evalJ (c x : ℂ) : EmlExpr → ℂ
  | .one => 1
  | .var => x
  | .app l r => Complex.exp (l.evalJ c x) -
      (if r.evalJ c x = 0 then c else Complex.log (r.evalJ c x))

/-! ## Main results -/

/-- **The reduction.** There is a computable translation of Richardson expressions into
    EML trees that preserves the value at every real `x` (0 and negative values included)
    and never takes `log 0` at any real input. -/
theorem compiler_exists :
    ∃ f : RExpr → EmlExpr, Computable f ∧
      ∀ (e : RExpr) (x : ℝ), (f e).evalC x = ((e.eval x : ℝ) : ℂ) ∧ Safe (x : ℂ) (f e) := by
  sorry

/-- **Zero-equivalence of EML trees is undecidable**, assuming Richardson's theorem. -/
theorem eml_zero_undecidable_final
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalC x = 0) := by
  sorry

/-- **Root existence for EML trees is undecidable**, assuming Richardson's theorem. -/
theorem eml_root_undecidable_final
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalC x = 0) := by
  sorry

/-- Zero-equivalence is undecidable with `log 0` **undefined**. -/
theorem eml_zero_undecidable_partial
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalO x = some 0) := by
  sorry

/-- Root existence is undecidable with `log 0` **undefined**. -/
theorem eml_root_undecidable_partial
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalO x = some 0) := by
  sorry

/-- Zero-equivalence is undecidable for **every** choice of the value `c` of `log 0`. -/
theorem eml_zero_undecidable_any (c : ℂ)
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalJ c x = 0) := by
  sorry

/-- Root existence is undecidable for **every** choice of the value `c` of `log 0`. -/
theorem eml_root_undecidable_any (c : ℂ)
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalJ c x = 0) := by
  sorry


/-! ## Further undecidable problems -/

/-- **Equivalence of two EML trees is undecidable**: whether they agree at every real `x`,
    assuming Richardson's theorem. -/
theorem eml_equiv_undecidable
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun p : EmlExpr × EmlExpr => ∀ x : ℝ, p.1.evalC x = p.2.evalC x) := by
  sorry

/-- **Negativity of an EML tree is undecidable**: whether it takes a negative real value
    at some real `x`, assuming Richardson's theorem. -/
theorem eml_neg_undecidable
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, ∃ r : ℝ, r < 0 ∧ t.evalC x = r) := by
  sorry

/-- **Constancy of an EML tree on ℝ is undecidable**, assuming Richardson's theorem. -/
theorem eml_const_undecidable
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ c : ℂ, ∀ x : ℝ, t.evalC x = c) := by
  sorry

end EmlRichardson

end
