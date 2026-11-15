module

public import Mathlib

/-!
# Solution: Richardson's theorem ⇒ EML zero/root problems undecidable
  Checked on live.lean-lang.org (Lean v4.36.0-rc2 + latest Mathlib), 2026-11-13.
  No `sorry`: every theorem depends only on propext, Classical.choice, Quot.sound.

  The only hypothesis of the final theorems (Part 7) is Richardson's theorem itself
  (stated against the explicit Gödel numbering of Part 1b, not proved here).
  The encodings and the computability of the compiler are proved (Parts 1b, 7a).

  Goal: formalize the reduction  Richardson's zero problem  ≤₀  EML zero problem,
  i.e. "deciding whether an EML tree is identically zero is undecidable".

  Structure
    Part 1  Syntax + semantics: Richardson expressions (RExpr) and EML trees (EmlExpr).
    Part 1b Gödel numberings RExpr ≃ ℕ, EmlExpr ≃ ℕ (`Primcodable`).    (proved)
    Part 2  A *gadget set*: one EML template per Richardson primitive, each with a
            correctness spec that must hold for EVERY real input (0 and negatives
            included). This is exactly the "branch cuts never bite" condition.
    Part 3  Generic compiler RExpr → EmlExpr and its correctness proof, by induction,
            given any gadget set.                                       (proved)
    Part 4  Corollaries: zero-equivalence and root-existence transfer.  (proved)
    Part 5  Undecidability transfer via many-one reduction, taking
            Richardson's theorem as a hypothesis.                       (proved)
    Part 6  The gadget set: exp, +, −, ×, |·|, ℚ, ln 2 (6a/6b, all-real
            computation), π and sin (6c, complex with branch control),
            assembled as `theGadgets` (6d).                             (proved)
    Part 7a The compiler `compile theGadgets` is primitive recursive.  (proved)
    Part 7  Main results specialised to `theGadgets`, assuming only
            Richardson's theorem.                                       (proved)
    Part 8  No compiled tree ever takes log 0, so the results hold with log 0
            undefined, or set to any value.                              (proved)
    Part 9  The statements of Challenge.lean, proved.                  (proved)


-/

@[expose] public section

namespace EmlRichardson

/-! ## Part 1 — Syntax and semantics -/

/-- Richardson's basis: rationals, π, ln 2, the variable x, +, ×, sin, exp, |·|.
    Closure under composition is automatic: composition = substitution for `var`.
    A rational is given by three naturals: `rat p q d` denotes (p − q)/(d + 1);
    every rational arises this way. Subtraction is `add a (mul (rat 0 1 0) b)`. -/
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

/-- One-variable EML trees: S → 1 | x | eml(S, S)  (same grammar as eml-lean). -/
inductive EmlExpr where
  | one
  | var
  | app (l r : EmlExpr)
  deriving DecidableEq, Repr

/-- Complex EML operator with Mathlib's principal `Complex.log`.
    NB: Mathlib is total — `Complex.log 0 = 0` is a junk value, not an error. -/
noncomputable def ceml (x y : ℂ) : ℂ := Complex.exp x - Complex.log y

/-- Complex semantics of an EML tree. Complex is needed: signed arithmetic and sin
    go through log of negative numbers and through i. -/
noncomputable def EmlExpr.evalC (x : ℂ) : EmlExpr → ℂ
  | .one     => 1
  | .var     => x
  | .app l r => ceml (l.evalC x) (r.evalC x)

/-! ## Part 1b — Gödel numberings (explicit bijections with ℕ)

These fix the `Primcodable` structures used in the decidability statements, so the
final theorems carry no encoding assumptions. -/

/-- one ↦ 0, x ↦ 1, eml(l, r) ↦ ⟨l, r⟩ + 2. -/
def encE : EmlExpr → ℕ
  | .one => 0
  | .var => 1
  | .app l r => Nat.pair (encE l) (encE r) + 2

def decE : ℕ → EmlExpr
  | 0 => .one
  | 1 => .var
  | n + 2 => .app (decE n.unpair.1) (decE n.unpair.2)
termination_by n => n
decreasing_by
  all_goals (have := Nat.unpair_left_le n; have := Nat.unpair_right_le n; omega)

theorem decE_encE : ∀ t, decE (encE t) = t
  | .one => by simp [encE, decE]
  | .var => by simp [encE, decE]
  | .app l r => by simp only [encE, decE, Nat.unpair_pair, decE_encE l, decE_encE r]

theorem encE_decE : ∀ n, encE (decE n) = n
  | 0 => by simp [encE, decE]
  | 1 => by simp [encE, decE]
  | n + 2 => by
    have := Nat.unpair_left_le n
    have := Nat.unpair_right_le n
    simp only [decE, encE, encE_decE n.unpair.1, encE_decE n.unpair.2, Nat.pair_unpair]
termination_by n => n
decreasing_by
  all_goals (have := Nat.unpair_left_le n; have := Nat.unpair_right_le n; omega)

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

theorem decR_encR : ∀ e, decR (encR e) = e
  | .pi => by simp [encR, decR]
  | .ln2 => by simp [encR, decR]
  | .var => by simp [encR, decR]
  | .rat p q d => by
    have h1 : 6 * Nat.pair p (Nat.pair q d) % 6 = 0 := by omega
    have h2 : 6 * Nat.pair p (Nat.pair q d) / 6 = Nat.pair p (Nat.pair q d) := by omega
    show decR (6 * Nat.pair p (Nat.pair q d) + 3) = _
    simp only [decR]; simp [h1, h2, Nat.unpair_pair]
  | .add a b => by
    have h1 : (6 * Nat.pair (encR a) (encR b) + 1) % 6 = 1 := by omega
    have h2 : (6 * Nat.pair (encR a) (encR b) + 1) / 6 = Nat.pair (encR a) (encR b) := by omega
    show decR (6 * Nat.pair (encR a) (encR b) + 1 + 3) = _
    simp only [decR]; simp [h1, h2, Nat.unpair_pair, decR_encR a, decR_encR b]
  | .mul a b => by
    have h1 : (6 * Nat.pair (encR a) (encR b) + 2) % 6 = 2 := by omega
    have h2 : (6 * Nat.pair (encR a) (encR b) + 2) / 6 = Nat.pair (encR a) (encR b) := by omega
    show decR (6 * Nat.pair (encR a) (encR b) + 2 + 3) = _
    simp only [decR]; simp [h1, h2, Nat.unpair_pair, decR_encR a, decR_encR b]
  | .sin a => by
    have h1 : (6 * encR a + 3) % 6 = 3 := by omega
    have h2 : (6 * encR a + 3) / 6 = encR a := by omega
    show decR (6 * encR a + 3 + 3) = _
    simp only [decR]; simp [h1, h2, decR_encR a]
  | .exp a => by
    have h1 : (6 * encR a + 4) % 6 = 4 := by omega
    have h2 : (6 * encR a + 4) / 6 = encR a := by omega
    show decR (6 * encR a + 4 + 3) = _
    simp only [decR]; simp [h1, h2, decR_encR a]
  | .abs a => by
    have h1 : (6 * encR a + 5) % 6 = 5 := by omega
    have h2 : (6 * encR a + 5) / 6 = encR a := by omega
    show decR (6 * encR a + 5 + 3) = _
    simp only [decR]; simp [h1, h2, decR_encR a]

theorem encR_decR : ∀ n, encR (decR n) = n
  | 0 => by simp [encR, decR]
  | 1 => by simp [encR, decR]
  | 2 => by simp [encR, decR]
  | n + 3 => by
    have := Nat.unpair_left_le (n / 6)
    have := Nat.unpair_right_le (n / 6)
    have := Nat.div_le_self n 6
    have := Nat.div_add_mod n 6
    simp only [decR]
    split_ifs
    · simp only [encR, Nat.pair_unpair]; omega
    · rw [encR, encR_decR (n / 6).unpair.1, encR_decR (n / 6).unpair.2, Nat.pair_unpair]; omega
    · rw [encR, encR_decR (n / 6).unpair.1, encR_decR (n / 6).unpair.2, Nat.pair_unpair]; omega
    · rw [encR, encR_decR (n / 6)]; omega
    · rw [encR, encR_decR (n / 6)]; omega
    · rw [encR, encR_decR (n / 6)]; omega
termination_by n => n
decreasing_by
  all_goals (have := Nat.unpair_left_le (n / 6); have := Nat.unpair_right_le (n / 6); have := Nat.div_le_self n 6; omega)

def eR : RExpr ≃ ℕ := ⟨encR, decR, decR_encR, encR_decR⟩

instance : Primcodable RExpr := Primcodable.ofEquiv ℕ eR

/-! ## Part 2 — Gadget specification

Each spec is conditional only on the *inputs being real numbers* (which is all a
Richardson expression ever produces), and must then hold for every real input.
No positivity, no "x ≠ 0", no branch-window hypotheses: a gadget that only works
on part of ℝ does not meet the spec. -/

structure Gadgets where
  rat  : ℕ → ℕ → ℕ → EmlExpr
  pi   : EmlExpr
  ln2  : EmlExpr
  add  : EmlExpr → EmlExpr → EmlExpr
  mul  : EmlExpr → EmlExpr → EmlExpr
  sin  : EmlExpr → EmlExpr
  exp  : EmlExpr → EmlExpr
  abs  : EmlExpr → EmlExpr
  rat_spec : ∀ (p q d : ℕ) (x : ℂ),
      (rat p q d).evalC x = ((((p : ℝ) - q) / (d + 1) : ℝ) : ℂ)
  pi_spec  : ∀ x : ℂ, pi.evalC x = ((Real.pi : ℝ) : ℂ)
  ln2_spec : ∀ x : ℂ, ln2.evalC x = ((Real.log 2 : ℝ) : ℂ)
  add_spec : ∀ (s t : EmlExpr) (x : ℂ) (a b : ℝ),
      s.evalC x = a → t.evalC x = b → (add s t).evalC x = ((a + b : ℝ) : ℂ)
  mul_spec : ∀ (s t : EmlExpr) (x : ℂ) (a b : ℝ),
      s.evalC x = a → t.evalC x = b → (mul s t).evalC x = ((a * b : ℝ) : ℂ)
  sin_spec : ∀ (s : EmlExpr) (x : ℂ) (a : ℝ),
      s.evalC x = a → (sin s).evalC x = ((Real.sin a : ℝ) : ℂ)
  exp_spec : ∀ (s : EmlExpr) (x : ℂ) (a : ℝ),
      s.evalC x = a → (exp s).evalC x = ((Real.exp a : ℝ) : ℂ)
  /-- The hard one: must give |a| for every real a, including a = 0. -/
  abs_spec : ∀ (s : EmlExpr) (x : ℂ) (a : ℝ),
      s.evalC x = a → (abs s).evalC x = ((|a| : ℝ) : ℂ)

/-! ## Part 3 — The compiler and its correctness -/

/-- Structural compiler. Computable as long as the gadget templates are. -/
def compile (G : Gadgets) : RExpr → EmlExpr
  | .rat p q d => G.rat p q d
  | .pi      => G.pi
  | .ln2     => G.ln2
  | .var     => .var
  | .add a b => G.add (compile G a) (compile G b)
  | .mul a b => G.mul (compile G a) (compile G b)
  | .sin a   => G.sin (compile G a)
  | .exp a   => G.exp (compile G a)
  | .abs a   => G.abs (compile G a)

/-- **Compiler correctness, everywhere on ℝ.** -/
theorem compile_correct (G : Gadgets) :
    ∀ (e : RExpr) (x : ℝ), (compile G e).evalC x = ((e.eval x : ℝ) : ℂ)
  | .rat p q d, x => G.rat_spec p q d x
  | .pi, x    => G.pi_spec x
  | .ln2, x   => G.ln2_spec x
  | .var, _   => rfl
  | .add a b, x =>
      G.add_spec (compile G a) (compile G b) x (a.eval x) (b.eval x)
        (compile_correct G a x) (compile_correct G b x)
  | .mul a b, x =>
      G.mul_spec (compile G a) (compile G b) x (a.eval x) (b.eval x)
        (compile_correct G a x) (compile_correct G b x)
  | .sin a, x => G.sin_spec (compile G a) x (a.eval x) (compile_correct G a x)
  | .exp a, x => G.exp_spec (compile G a) x (a.eval x) (compile_correct G a x)
  | .abs a, x => G.abs_spec (compile G a) x (a.eval x) (compile_correct G a x)

/-! ## Part 4 — The two decision problems transfer -/

/-- Identically-zero problem transfers. -/
theorem zero_iff (G : Gadgets) (e : RExpr) :
    (∀ x : ℝ, e.eval x = 0) ↔ (∀ x : ℝ, (compile G e).evalC x = 0) := by
  simp only [compile_correct, Complex.ofReal_eq_zero]

/-- Root-existence problem transfers. -/
theorem root_iff (G : Gadgets) (e : RExpr) :
    (∃ x : ℝ, e.eval x = 0) ↔ (∃ x : ℝ, (compile G e).evalC x = 0) := by
  simp only [compile_correct, Complex.ofReal_eq_zero]

/-! ## Part 5 — Undecidability transfer

Uses the Gödel numberings of Part 1b. Richardson's theorem enters as a hypothesis
stated against the same numbering of `RExpr`. -/

section Undecidability

/-- Zero-equivalence of EML trees (over the reals) is undecidable. -/
theorem eml_zero_undecidable (G : Gadgets) (hG : Computable (compile G))
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalC x = 0) := fun h =>
  richardson (ComputablePred.computable_of_manyOneReducible
    ⟨compile G, hG, fun e => zero_iff G e⟩ h)

/-- Root existence for EML trees (over the reals) is undecidable. -/
theorem eml_root_undecidable (G : Gadgets) (hG : Computable (compile G))
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalC x = 0) := fun h =>
  richardson (ComputablePred.computable_of_manyOneReducible
    ⟨compile G, hG, fun e => root_iff G e⟩ h)

end Undecidability

/-! ## Part 6 — Constructing the gadgets

### One gadget that is easy: exp
`eml(s, 1) = exp s − log 1 = exp s`, with no branch condition at all. -/

def expG (s : EmlExpr) : EmlExpr := .app s .one

theorem expG_spec (s : EmlExpr) (x : ℂ) (a : ℝ) (h : s.evalC x = a) :
    (expG s).evalC x = ((Real.exp a : ℝ) : ℂ) := by
  simp [expG, EmlExpr.evalC, ceml, h, Complex.log_one, Complex.ofReal_exp]

/-! ### Part 6a — Real-valued toolkit: exp, +, −, ×, |·| for EVERY real input

Key idea: never take `log` of a value that can be negative. Every right-hand child
of an `app` node below evaluates to a real number `p ≥ 0`, where the principal
complex log agrees with `Real.log` (including the junk value `log 0 = 0`).
So the whole computation stays inside ℝ and no branch cut is ever touched.
Signed quantities are handled by writing them as differences of positives:
`a = eᵃ − (eᵃ − a)`, where `eᵃ − a ≥ 1`. -/

theorem one_eval (x : ℂ) : EmlExpr.one.evalC x = ((1 : ℝ) : ℂ) := by
  simp [EmlExpr.evalC]

/-- One `eml` node on real inputs, right input `p ≥ 0`. -/
theorem app_eval {l r : EmlExpr} {x : ℂ} {a p : ℝ}
    (hl : l.evalC x = (a : ℂ)) (hr : r.evalC x = (p : ℂ)) (hp : 0 ≤ p) :
    (EmlExpr.app l r).evalC x = ((Real.exp a - Real.log p : ℝ) : ℂ) := by
  simp only [EmlExpr.evalC, ceml, hl, hr]
  rw [Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_log hp]

/-- exp:  eml(s, 1) = eˢ. -/
def gE (s : EmlExpr) : EmlExpr := .app s .one

theorem gE_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gE s).evalC x = ((Real.exp a : ℝ) : ℂ) := by
  rw [gE, app_eval hs (one_eval x) zero_le_one, Real.log_one, sub_zero]

/-- D(s, t) = eml(s, exp t) = eˢ − t, for all real s, t. -/
def gD (s t : EmlExpr) : EmlExpr := .app s (gE t)

theorem gD_spec {s t : EmlExpr} {x : ℂ} {a b : ℝ}
    (hs : s.evalC x = (a : ℂ)) (ht : t.evalC x = (b : ℂ)) :
    (gD s t).evalC x = ((Real.exp a - b : ℝ) : ℂ) := by
  rw [gD, app_eval hs (gE_spec ht) (Real.exp_pos b).le, Real.log_exp]

/-- log, paper eq. (5): eml(1, eml(eml(1, s), 1)); correct for every p ≥ 0
    (at p = 0 it returns Mathlib's junk value `Real.log 0 = 0`). -/
def gL (s : EmlExpr) : EmlExpr := .app .one (gE (.app .one s))

theorem gL_spec {s : EmlExpr} {x : ℂ} {p : ℝ} (hs : s.evalC x = (p : ℂ)) (hp : 0 ≤ p) :
    (gL s).evalC x = ((Real.log p : ℝ) : ℂ) := by
  rw [gL, app_eval (one_eval x) (gE_spec (app_eval (one_eval x) hs hp))
      (Real.exp_pos _).le, Real.log_exp]
  congr 1; ring

/-- p − q for p > 0:  eml(log p, exp q). -/
def gSub (s t : EmlExpr) : EmlExpr := .app (gL s) (gE t)

theorem gSub_spec {s t : EmlExpr} {x : ℂ} {p q : ℝ}
    (hs : s.evalC x = (p : ℂ)) (ht : t.evalC x = (q : ℂ)) (hp : 0 < p) :
    (gSub s t).evalC x = ((p - q : ℝ) : ℂ) := by
  rw [gSub, app_eval (gL_spec hs hp.le) (gE_spec ht) (Real.exp_pos q).le,
    Real.exp_log hp, Real.log_exp]

/-- **Addition, for all real a, b**:  a + b = D(a, (eᵃ − a) − b),
    and eᵃ − a ≥ 1 > 0, so `gSub` never sees 0. -/
def gAdd (s t : EmlExpr) : EmlExpr := gD s (gSub (gD s s) t)

theorem gAdd_spec {s t : EmlExpr} {x : ℂ} {a b : ℝ}
    (hs : s.evalC x = (a : ℂ)) (ht : t.evalC x = (b : ℂ)) :
    (gAdd s t).evalC x = ((a + b : ℝ) : ℂ) := by
  have hpos : 0 < Real.exp a - a := by linarith [Real.add_one_le_exp a]
  rw [gAdd, gD_spec hs (gSub_spec (gD_spec hs hs) ht hpos)]
  congr 1; ring

/-- The constant 0 = log 1 (paper: K = 7). -/
def gZero : EmlExpr := gL .one

theorem gZero_spec (x : ℂ) : gZero.evalC x = ((0 : ℝ) : ℂ) := by
  rw [gZero, gL_spec (one_eval x) zero_le_one, Real.log_one]

/-- **Negation, for all real b**:  −b = e⁰ − (1 + b). -/
def gNeg (t : EmlExpr) : EmlExpr := gD gZero (gAdd .one t)

theorem gNeg_spec {t : EmlExpr} {x : ℂ} {b : ℝ} (ht : t.evalC x = (b : ℂ)) :
    (gNeg t).evalC x = ((-b : ℝ) : ℂ) := by
  rw [gNeg, gD_spec (gZero_spec x) (gAdd_spec (one_eval x) ht), Real.exp_zero]
  congr 1; ring

/-- Product of two positives:  p·q = exp(log p + log q). -/
def gPosMul (s t : EmlExpr) : EmlExpr := gE (gAdd (gL s) (gL t))

theorem gPosMul_spec {s t : EmlExpr} {x : ℂ} {p q : ℝ}
    (hs : s.evalC x = (p : ℂ)) (ht : t.evalC x = (q : ℂ)) (hp : 0 < p) (hq : 0 < q) :
    (gPosMul s t).evalC x = ((p * q : ℝ) : ℂ) := by
  rw [gPosMul, gE_spec (gAdd_spec (gL_spec hs hp.le) (gL_spec ht hq.le)),
    Real.exp_add, Real.exp_log hp, Real.exp_log hq]

/-- **Multiplication, for all real a, b** (0 and negatives included):
    with a = P₁ − P₂, b = Q₁ − Q₂ where P₁ = eᵃ, P₂ = eᵃ − a (both > 0),
    ab = P₁Q₁ − P₁Q₂ − P₂Q₁ + P₂Q₂, and every product is of positives. -/
def gMul (s t : EmlExpr) : EmlExpr :=
  gAdd (gAdd (gPosMul (gE s) (gE t)) (gNeg (gPosMul (gE s) (gD t t))))
       (gAdd (gNeg (gPosMul (gD s s) (gE t))) (gPosMul (gD s s) (gD t t)))

theorem gMul_spec {s t : EmlExpr} {x : ℂ} {a b : ℝ}
    (hs : s.evalC x = (a : ℂ)) (ht : t.evalC x = (b : ℂ)) :
    (gMul s t).evalC x = ((a * b : ℝ) : ℂ) := by
  have pa1 : 0 < Real.exp a := Real.exp_pos a
  have pb1 : 0 < Real.exp b := Real.exp_pos b
  have pa2 : 0 < Real.exp a - a := by linarith [Real.add_one_le_exp a]
  have pb2 : 0 < Real.exp b - b := by linarith [Real.add_one_le_exp b]
  have hP1 := gE_spec hs
  have hQ1 := gE_spec ht
  have hP2 := gD_spec hs hs
  have hQ2 := gD_spec ht ht
  rw [gMul, gAdd_spec
    (gAdd_spec (gPosMul_spec hP1 hQ1 pa1 pb1) (gNeg_spec (gPosMul_spec hP1 hQ2 pa1 pb2)))
    (gAdd_spec (gNeg_spec (gPosMul_spec hP2 hQ1 pa2 pb1)) (gPosMul_spec hP2 hQ2 pa2 pb2))]
  congr 1; ring

/-- The constant 1/2 = exp(−log 2). -/
def gHalf : EmlExpr := gE (gNeg (gL (gAdd .one .one)))

theorem gHalf_spec (x : ℂ) : gHalf.evalC x = ((1 / 2 : ℝ) : ℂ) := by
  rw [gHalf, gE_spec (gNeg_spec (gL_spec (gAdd_spec (one_eval x) (one_eval x))
      (by norm_num)))]
  congr 1
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-! ### Part 6b — Constants: naturals, integers, rationals, ln 2 -/

/-- Natural numbers: n = 0 + 1 + ... + 1. -/
def gNat : ℕ → EmlExpr
  | 0 => gZero
  | n + 1 => gAdd (gNat n) .one

theorem gNat_spec (n : ℕ) (x : ℂ) : (gNat n).evalC x = ((n : ℝ) : ℂ) := by
  induction n with
  | zero => rw [gNat, Nat.cast_zero]; exact gZero_spec x
  | succ n ih => rw [gNat, gAdd_spec ih (one_eval x), Nat.cast_succ]

/-- Integers: negatives via gNeg. -/
def gInt : ℤ → EmlExpr
  | .ofNat n => gNat n
  | .negSucc n => gNeg (gNat (n + 1))

theorem gInt_spec (z : ℤ) (x : ℂ) : (gInt z).evalC x = ((z : ℝ) : ℂ) := by
  cases z with
  | ofNat n => simp only [gInt, gNat_spec]; simp
  | negSucc n => simp only [gInt]; rw [gNeg_spec (gNat_spec (n + 1) x)]; simp [Int.cast_negSucc]

/-- Rationals: q = num · exp(−log den). -/
def gRat (q : ℚ) : EmlExpr := gMul (gInt q.num) (gE (gNeg (gL (gNat q.den))))

theorem gRat_spec (q : ℚ) (x : ℂ) : (gRat q).evalC x = ((q : ℝ) : ℂ) := by
  have hden : (0 : ℝ) < q.den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero q.den_nz)
  rw [gRat, gMul_spec (gInt_spec _ x)
    (gE_spec (gNeg_spec (gL_spec (gNat_spec _ x) hden.le)))]
  congr 1
  rw [Real.exp_neg, Real.exp_log hden, Rat.cast_def, div_eq_mul_inv]

/-- The rational (p − q)/(d + 1) = (p + (−q)) · exp(−log(d + 1)). -/
def gFrac (p q d : ℕ) : EmlExpr :=
  gMul (gAdd (gNat p) (gNeg (gNat q))) (gE (gNeg (gL (gNat (d + 1)))))

theorem gFrac_spec (p q d : ℕ) (x : ℂ) :
    (gFrac p q d).evalC x = ((((p : ℝ) - q) / (d + 1) : ℝ) : ℂ) := by
  have hden : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  rw [gFrac, gMul_spec (gAdd_spec (gNat_spec p x) (gNeg_spec (gNat_spec q x)))
    (gE_spec (gNeg_spec (gL_spec (gNat_spec (d + 1) x) hden.le)))]
  congr 1
  rw [Real.exp_neg, Real.exp_log hden]
  push_cast
  ring

/-- ln 2 = log(1 + 1). -/
def gLn2 : EmlExpr := gL (gNat 2)

theorem gLn2_spec (x : ℂ) : gLn2.evalC x = ((Real.log 2 : ℝ) : ℂ) := by
  rw [gLn2, gL_spec (gNat_spec 2 x) (Nat.cast_nonneg _)]
  norm_num

/-! ### Part 6c — Complex lemmas, π and sin

π and sin need complex intermediate values. Every `log` below is applied either to a
value whose principal log is known (−1, −iπ), or inside `log (exp w)` with
|Im w| ≤ 1 or |Im w| = π/2, so it is always on the principal branch. -/

theorem evalC_app (l r : EmlExpr) (x : ℂ) :
    (EmlExpr.app l r).evalC x = Complex.exp (l.evalC x) - Complex.log (r.evalC x) := rfl

theorem gE_C (s : EmlExpr) (x : ℂ) : (gE s).evalC x = Complex.exp (s.evalC x) := by
  simp only [gE, EmlExpr.evalC, ceml, Complex.log_one, sub_zero]

theorem gD_C {s t : EmlExpr} {x : ℂ} (h1 : -Real.pi < (t.evalC x).im)
    (h2 : (t.evalC x).im ≤ Real.pi) :
    (gD s t).evalC x = Complex.exp (s.evalC x) - t.evalC x := by
  simp only [gD, gE, EmlExpr.evalC, ceml, Complex.log_one, sub_zero]
  rw [Complex.log_exp h1 h2]

/-- exp ∘ (log gadget) = id on ℂ \ {0}: any branch error of gL is killed by exp. -/
theorem exp_gL {s : EmlExpr} {x : ℂ} (h : s.evalC x ≠ 0) :
    Complex.exp ((gL s).evalC x) = s.evalC x := by
  simp only [gL, gE, EmlExpr.evalC, ceml, Complex.log_one, sub_zero]
  rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero _), Complex.exp_sub,
    Complex.exp_log h]
  field_simp

theorem exp_one_im : (Complex.exp 1).im = 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp, Complex.ofReal_im]

/-- gL is the principal log off the negative real axis. -/
theorem gL_C {s : EmlExpr} {x : ℂ} (h : (Complex.log (s.evalC x)).im < Real.pi) :
    (gL s).evalC x = Complex.log (s.evalC x) := by
  simp only [gL, gE, EmlExpr.evalC, ceml, Complex.log_one, sub_zero]
  have him : (Complex.exp 1 - Complex.log (s.evalC x)).im = -(Complex.log (s.evalC x)).im := by
    rw [Complex.sub_im, exp_one_im, zero_sub]
  rw [Complex.log_exp (by rw [him]; linarith)
    (by rw [him]; linarith [Complex.neg_pi_lt_log_im (s.evalC x)])]
  ring

theorem gSub_C {s t : EmlExpr} {x : ℂ} (hs : s.evalC x ≠ 0)
    (h1 : -Real.pi < (t.evalC x).im) (h2 : (t.evalC x).im ≤ Real.pi) :
    (gSub s t).evalC x = s.evalC x - t.evalC x := by
  rw [gSub, evalC_app, exp_gL hs, gE_C, Complex.log_exp h1 h2]

/-- real + complex, when |Im b| < π. -/
theorem gAdd_RC {s t : EmlExpr} {x : ℂ} {a : ℝ} {b : ℂ}
    (hs : s.evalC x = (a : ℂ)) (ht : t.evalC x = b)
    (h1 : -Real.pi < b.im) (h2 : b.im < Real.pi) :
    (gAdd s t).evalC x = (a : ℂ) + b := by
  have hp : 0 < Real.exp a - a := by linarith [Real.add_one_le_exp a]
  have hDss := gD_spec hs hs
  have hne : (gD s s).evalC x ≠ 0 := by rw [hDss]; exact_mod_cast hp.ne'
  have hsub := gSub_C (t := t) hne (by rw [ht]; exact h1) (by rw [ht]; exact h2.le)
  rw [hDss, ht] at hsub
  have him : ((gSub (gD s s) t).evalC x).im = -b.im := by
    rw [hsub, Complex.sub_im, Complex.ofReal_im, zero_sub]
  rw [gAdd, gD_C (by rw [him]; linarith) (by rw [him]; linarith), hsub, hs]
  push_cast
  ring

theorem gNeg_C {t : EmlExpr} {x : ℂ} {b : ℂ} (ht : t.evalC x = b)
    (h1 : -Real.pi < b.im) (h2 : b.im < Real.pi) : (gNeg t).evalC x = -b := by
  have hadd := gAdd_RC (one_eval x) ht h1 h2
  have him : ((gAdd .one t).evalC x).im = b.im := by
    rw [hadd, Complex.add_im, Complex.ofReal_im, zero_add]
  rw [gNeg, gD_C (by rw [him]; exact h1) (by rw [him]; exact h2.le), hadd, gZero_spec]
  rw [Complex.ofReal_zero, Complex.exp_zero, Complex.ofReal_one]
  ring

theorem im_hp : (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im = Real.pi / 2 := by
  rw [Complex.mul_I_im, Complex.ofReal_re]

theorem exp_half_pi_I : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

theorem exp_neg_half_pi_I :
    Complex.exp (-(((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) = -Complex.I := by
  rw [Complex.exp_neg, exp_half_pi_I, Complex.inv_I]

/-- V = log-gadget(−1) = −iπ (the gadget lands on the shifted branch). -/
def gV : EmlExpr := gL (gNeg .one)

/-- The log gadget applied to −1 gives −iπ (the other end of the branch cut). -/
theorem gL_neg_one {s : EmlExpr} {x : ℂ} (h1 : s.evalC x = -1) :
    (gL s).evalC x = -((Real.pi : ℂ) * Complex.I) := by
  simp only [gL, gE, EmlExpr.evalC, ceml, Complex.log_one, sub_zero]
  rw [h1, Complex.log_neg_one]
  have key : Complex.exp (Complex.exp 1 - (Real.pi : ℂ) * Complex.I)
      = Complex.exp (Complex.exp 1 + (Real.pi : ℂ) * Complex.I) := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have him : (Complex.exp 1 + (Real.pi : ℂ) * Complex.I).im = Real.pi := by
    rw [Complex.add_im, exp_one_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  rw [key, Complex.log_exp (by rw [him]; linarith [Real.pi_pos]) him.le]
  ring

theorem gV_spec (x : ℂ) : gV.evalC x = -((Real.pi : ℂ) * Complex.I) :=
  gL_neg_one (by rw [gNeg_spec (one_eval x)]; simp)

theorem hV0 : -((Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]

theorem log_V_im : (Complex.log (-((Real.pi : ℂ) * Complex.I))).im = -(Real.pi / 2) := by
  rw [Complex.log_im, show -((Real.pi : ℂ) * Complex.I) = (Real.pi : ℂ) * (-Complex.I) by ring,
    Complex.arg_real_mul _ Real.pi_pos, Complex.arg_neg_I]

theorem gLV_spec (x : ℂ) :
    (gL gV).evalC x = Complex.log (-((Real.pi : ℂ) * Complex.I)) := by
  rw [gL_C (by rw [gV_spec, log_V_im]; linarith [Real.pi_pos]), gV_spec]

theorem gLV_ne (x : ℂ) : (gL gV).evalC x ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [gLV_spec, log_V_im, Complex.zero_im] at this
  linarith [Real.pi_pos]

/-- C = exp(log ½ + log(−iπ)) = −iπ/2. -/
def gC : EmlExpr := gE (gAdd (gL gHalf) (gL gV))

theorem gC_spec (x : ℂ) : gC.evalC x = -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  have hLH := gL_spec (gHalf_spec x) (by norm_num : (0:ℝ) ≤ 1 / 2)
  rw [gC, gE_C, gAdd_RC hLH (gLV_spec x) (by rw [log_V_im]; linarith [Real.pi_pos])
      (by rw [log_V_im]; linarith [Real.pi_pos]),
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by norm_num), Complex.exp_log hV0]
  push_cast
  ring

/-- **π** = exp(log(−iπ) − (−iπ/2)) = (−iπ)/(−i). -/
def gPi : EmlExpr := gE (gSub (gL gV) gC)

theorem gPi_spec (x : ℂ) : gPi.evalC x = ((Real.pi : ℝ) : ℂ) := by
  have hne : (gL gV).evalC x ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [gLV_spec, log_V_im, Complex.zero_im] at this
    linarith [Real.pi_pos]
  have hCim : (gC.evalC x).im = -(Real.pi / 2) := by rw [gC_spec, Complex.neg_im, im_hp]
  rw [gPi, gE_C, gSub_C hne (by rw [hCim]; linarith [Real.pi_pos])
      (by rw [hCim]; linarith [Real.pi_pos]),
    Complex.exp_sub, gLV_spec, Complex.exp_log hV0, gC_spec, exp_neg_half_pi_I,
    neg_div_neg_eq, mul_div_assoc, div_self Complex.I_ne_zero, mul_one]

/-- iπ/2 = −C. -/
def gIH : EmlExpr := gNeg gC

theorem gIH_spec (x : ℂ) : gIH.evalC x = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gIH, gNeg_C (gC_spec x) (by rw [Complex.neg_im, im_hp]; linarith [Real.pi_pos])
    (by rw [Complex.neg_im, im_hp]; linarith [Real.pi_pos]), neg_neg]

/-- iP = exp(log P + iπ/2) for P > 0. -/
def giP (P : EmlExpr) : EmlExpr := gE (gAdd (gL P) gIH)

theorem giP_spec {P : EmlExpr} {x : ℂ} {p : ℝ} (hP : P.evalC x = (p : ℂ)) (hp : 0 < p) :
    (giP P).evalC x = (p : ℂ) * Complex.I := by
  rw [giP, gE_C, gAdd_RC (gL_spec hP hp.le) (gIH_spec x)
      (by rw [im_hp]; linarith [Real.pi_pos]) (by rw [im_hp]; linarith [Real.pi_pos]),
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hp, exp_half_pi_I]

/-- −iP = exp(log P − iπ/2) for P > 0. -/
def gmiP (P : EmlExpr) : EmlExpr := gE (gAdd (gL P) gC)

theorem gmiP_spec {P : EmlExpr} {x : ℂ} {p : ℝ} (hP : P.evalC x = (p : ℂ)) (hp : 0 < p) :
    (gmiP P).evalC x = -((p : ℂ) * Complex.I) := by
  rw [gmiP, gE_C, gAdd_RC (gL_spec hP hp.le) (gC_spec x)
      (by rw [Complex.neg_im, im_hp]; linarith [Real.pi_pos])
      (by rw [Complex.neg_im, im_hp]; linarith [Real.pi_pos]),
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hp, exp_neg_half_pi_I]
  ring

/-- 2·cos P = e^{iP} + e^{−iP} for P > 0; every log sees |Im| ≤ 1 < π. -/
def gCos2 (P : EmlExpr) : EmlExpr :=
  gD (giP P) (gD gZero (gD (gmiP P) (gNeg .one)))

theorem gCos2_spec {P : EmlExpr} {x : ℂ} {p : ℝ} (hP : P.evalC x = (p : ℂ)) (hp : 0 < p) :
    (gCos2 P).evalC x = ((2 * Real.cos p : ℝ) : ℂ) := by
  have hm := gmiP_spec hP hp
  have hi := giP_spec hP hp
  have hw : (Complex.exp (-((p : ℂ) * Complex.I))).im = -Real.sin p := by
    rw [show -((p : ℂ) * Complex.I) = ((-p : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  have hs1 := Real.sin_le_one p
  have hs2 := Real.neg_one_le_sin p
  have hπ := Real.pi_gt_three
  have hn1 : (gNeg EmlExpr.one).evalC x = ((-1 : ℝ) : ℂ) := gNeg_spec (one_eval x)
  have hT1 : (gD (gmiP P) (gNeg .one)).evalC x = Complex.exp (-((p : ℂ) * Complex.I)) + 1 := by
    rw [gD_C (by rw [hn1, Complex.ofReal_im]; linarith) (by rw [hn1, Complex.ofReal_im]; linarith),
      hm, hn1]
    push_cast
    ring
  have hT1im : ((gD (gmiP P) (gNeg .one)).evalC x).im = -Real.sin p := by
    rw [hT1, Complex.add_im, hw, Complex.one_im, add_zero]
  have hT2 : (gD gZero (gD (gmiP P) (gNeg .one))).evalC x
      = -Complex.exp (-((p : ℂ) * Complex.I)) := by
    rw [gD_C (by rw [hT1im]; linarith) (by rw [hT1im]; linarith), hT1, gZero_spec,
      Complex.ofReal_zero, Complex.exp_zero]
    ring
  have hT2im : ((gD gZero (gD (gmiP P) (gNeg .one))).evalC x).im = Real.sin p := by
    rw [hT2, Complex.neg_im, hw, neg_neg]
  rw [gCos2, gD_C (by rw [hT2im]; linarith) (by rw [hT2im]; linarith), hT2, hi,
    Complex.exp_mul_I, show -((p : ℂ) * Complex.I) = (-(p : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-! #### Absolute value without ever taking log 0

|a| = a · sign(a), and the sign is read off the branch cut of `log`.
Let g(a) = 1/(1 + e⁻ᵃ) − ½, which has the sign of a and |g| < ½, and u = 1 + i·g.
Then u ≠ 0, −u ≠ 0, and the log gadget gives
  gL(−u) − log u = −iπ  if a ≥ 0,   +iπ  if a < 0
(at a = 0, u = 1 and gL(−1) = −iπ). Every log in the tree gets a nonzero argument. -/

theorem exp_gSub {s t : EmlExpr} {x : ℂ} (hs : s.evalC x ≠ 0) :
    Complex.exp ((gSub s t).evalC x) = Complex.exp (s.evalC x - t.evalC x) := by
  rw [gSub, evalC_app, exp_gL hs, gE_C, Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero _),
    ← Complex.exp_sub]

/-- g(a) = 1/(1 + e^{−a}) − 1/2. -/
noncomputable def sg (a : ℝ) : ℝ := (1 + Real.exp (-a))⁻¹ - 1 / 2

theorem sg_eq (a : ℝ) : sg a = (1 - Real.exp (-a)) / (2 * (1 + Real.exp (-a))) := by
  have h : (1 + Real.exp (-a)) ≠ 0 := by positivity
  unfold sg
  field_simp
  ring

theorem sg_pos {a : ℝ} (ha : 0 < a) : 0 < sg a := by
  have h := Real.exp_lt_exp.mpr (by linarith : -a < 0)
  rw [Real.exp_zero] at h
  rw [sg_eq]
  apply div_pos
  · linarith
  · positivity

theorem sg_neg {a : ℝ} (ha : a < 0) : sg a < 0 := by
  have h := Real.exp_lt_exp.mpr (by linarith : (0 : ℝ) < -a)
  rw [Real.exp_zero] at h
  rw [sg_eq]
  apply div_neg_of_neg_of_pos
  · linarith
  · positivity

theorem sg_zero : sg 0 = 0 := by norm_num [sg]

theorem sg_lt (a : ℝ) : sg a < 1 / 2 := by
  rw [sg_eq, div_lt_iff₀ (by positivity)]
  linarith [Real.exp_pos (-a)]

theorem lt_sg (a : ℝ) : -(1 / 2) < sg a := by
  rw [sg_eq, lt_div_iff₀ (by positivity)]
  linarith [Real.exp_pos (-a)]

/-- π · sign(a), with sign(0) = 1. -/
noncomputable def sgnPi (a : ℝ) : ℝ := if 0 ≤ a then Real.pi else -Real.pi

theorem sgnPi_ne (a : ℝ) : sgnPi a ≠ 0 := by
  unfold sgnPi; split_ifs <;> simp [Real.pi_ne_zero]

theorem u_ne (r : ℝ) : (1 + (r : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem log_neg_sub_log_pos {u : ℂ} (h : 0 < u.im) :
    Complex.log (-u) - Complex.log u = -((Real.pi : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [Complex.log_re]
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
    simp

theorem log_neg_sub_log_neg {u : ℂ} (h : u.im < 0) :
    Complex.log (-u) - Complex.log u = (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
    simp

/-- σ(a) = 1/(1 + e^{−a}) ∈ (0, 1). -/
def gSig (s : EmlExpr) : EmlExpr := gE (gNeg (gL (gAdd .one (gE (gNeg s)))))

theorem gSig_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gSig s).evalC x = (((1 + Real.exp (-a))⁻¹ : ℝ) : ℂ) := by
  have hpos : 0 < 1 + Real.exp (-a) := by positivity
  rw [gSig, gE_spec (gNeg_spec (gL_spec (gAdd_spec (one_eval x) (gE_spec (gNeg_spec hs))) hpos.le)),
    Real.exp_neg (Real.log (1 + Real.exp (-a))), Real.exp_log hpos]

/-- W = i·g(a) = iσ(a) − i/2, computed exactly (every imaginary part is below 1). -/
def gW (s : EmlExpr) : EmlExpr := gSub (giP (gSig s)) (giP gHalf)

theorem giP_sig_ne {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (giP (gSig s)).evalC x ≠ 0 := by
  have hpos : 0 < 1 + Real.exp (-a) := by positivity
  rw [giP_spec (gSig_spec hs) (inv_pos.mpr hpos)]
  exact mul_ne_zero (by exact_mod_cast (inv_pos.mpr hpos).ne') Complex.I_ne_zero

theorem gW_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gW s).evalC x = ((sg a : ℝ) : ℂ) * Complex.I := by
  have hpos : 0 < 1 + Real.exp (-a) := by positivity
  have h1 := giP_spec (gSig_spec hs) (inv_pos.mpr hpos)
  have h2 := giP_spec (gHalf_spec x) (by norm_num : (0:ℝ) < 1 / 2)
  have him : ((giP gHalf).evalC x).im = 1 / 2 := by rw [h2, Complex.mul_I_im, Complex.ofReal_re]
  rw [gW, gSub_C (giP_sig_ne hs) (by rw [him]; linarith [Real.pi_pos])
    (by rw [him]; linarith [Real.pi_gt_three]), h1, h2, sg]
  push_cast
  ring

/-- u = 1 + i·g(a). -/
def gU (s : EmlExpr) : EmlExpr := gAdd .one (gW s)

theorem gU_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gU s).evalC x = 1 + ((sg a : ℝ) : ℂ) * Complex.I := by
  have him : (((sg a : ℝ) : ℂ) * Complex.I).im = sg a := by
    rw [Complex.mul_I_im, Complex.ofReal_re]
  have := sg_lt a
  have := lt_sg a
  have := Real.pi_gt_three
  rw [gU, gAdd_RC (one_eval x) (gW_spec hs) (by rw [him]; linarith) (by rw [him]; linarith),
    Complex.ofReal_one]

/-- −u. -/
def gZ (s : EmlExpr) : EmlExpr := gNeg (gU s)

theorem gZ_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gZ s).evalC x = -(1 + ((sg a : ℝ) : ℂ) * Complex.I) := by
  have him : (1 + ((sg a : ℝ) : ℂ) * Complex.I).im = sg a := by simp
  have := sg_lt a
  have := lt_sg a
  have := Real.pi_gt_three
  rw [gZ, gNeg_C (gU_spec hs) (by rw [him]; linarith) (by rw [him]; linarith)]

theorem gLZ_ne {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gL (gZ s)).evalC x ≠ 0 := by
  intro h
  have h2 := exp_gL (s := gZ s) (x := x) (by rw [gZ_spec hs]; exact neg_ne_zero.mpr (u_ne _))
  rw [h, Complex.exp_zero, gZ_spec hs] at h2
  have := congrArg Complex.re h2
  norm_num at this

/-- T = gL(−u) − log u = −iπ·sign(a). -/
def gT (s : EmlExpr) : EmlExpr := gSub (gL (gZ s)) (gL (gU s))

theorem gT_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gT s).evalC x = -((sgnPi a : ℂ) * Complex.I) := by
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = 1 + ((sg a : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
  have hU := gU_spec hs
  have hZ := gZ_spec hs
  rw [← hu] at hU hZ
  have huim : u.im = sg a := by rw [hu]; simp
  have hure : u.re = 1 := by rw [hu]; simp
  have hLU : (gL (gU s)).evalC x = Complex.log u := by
    have hlt : (Complex.log ((gU s).evalC x)).im < Real.pi := by
      rw [hU, Complex.log_im]
      exact Complex.arg_lt_pi_iff.mpr (Or.inl (by rw [hure]; norm_num))
    rw [gL_C hlt, hU]
  have hb1 : -Real.pi < ((gL (gU s)).evalC x).im := by
    rw [hLU, Complex.log_im]; exact Complex.neg_pi_lt_arg u
  have hb2 : ((gL (gU s)).evalC x).im ≤ Real.pi := by
    rw [hLU, Complex.log_im]; exact Complex.arg_le_pi u
  rw [gT, gSub_C (gLZ_ne hs) hb1 hb2, hLU]
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have him : u.im < 0 := by rw [huim]; exact sg_neg ha
    have hlt : (Complex.log ((gZ s).evalC x)).im < Real.pi := by
      rw [hZ, Complex.log_im]
      exact Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [Complex.neg_im]; exact neg_ne_zero.mpr him.ne))
    rw [gL_C hlt, hZ, log_neg_sub_log_neg him]
    simp only [sgnPi, not_le.mpr ha, ↓reduceIte]
    push_cast
    ring
  · have hz1 : (gZ s).evalC x = -1 := by rw [hZ, hu, sg_zero]; simp
    have hu1 : u = 1 := by rw [hu, sg_zero]; simp
    rw [gL_neg_one hz1, hu1, Complex.log_one, sub_zero]
    simp only [sgnPi, le_refl, ↓reduceIte]
  · have him : 0 < u.im := by rw [huim]; exact sg_pos ha
    have hlt : (Complex.log ((gZ s).evalC x)).im < Real.pi := by
      rw [hZ, Complex.log_im]
      exact Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [Complex.neg_im]; exact neg_ne_zero.mpr him.ne'))
    rw [gL_C hlt, hZ, log_neg_sub_log_pos him]
    simp only [sgnPi, ha.le, ↓reduceIte]

theorem gT_ne {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gT s).evalC x ≠ 0 := by
  rw [gT_spec hs]
  refine neg_ne_zero.mpr (mul_ne_zero ?_ Complex.I_ne_zero)
  exact_mod_cast sgnPi_ne a

theorem gLT_ne {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gL (gT s)).evalC x ≠ 0 := by
  intro h
  have h2 := exp_gL (gT_ne hs)
  rw [h, Complex.exp_zero, gT_spec hs] at h2
  have := congrArg Complex.im h2
  simp only [Complex.one_im, Complex.neg_im, Complex.mul_I_im, Complex.ofReal_re] at this
  exact sgnPi_ne a (by linarith)

/-- R = exp(log T + iπ/2) = i·T = π·sign(a), a real number. -/
def gR (s : EmlExpr) : EmlExpr := gE (gSub (gL (gT s)) gC)

theorem gR_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gR s).evalC x = ((sgnPi a : ℝ) : ℂ) := by
  rw [gR, gE_C, exp_gSub (gLT_ne hs), Complex.exp_sub, exp_gL (gT_ne hs), gT_spec hs, gC_spec,
    exp_neg_half_pi_I, neg_div_neg_eq, mul_div_assoc, div_self Complex.I_ne_zero, mul_one]

/-- 1/π = exp(−log π). -/
def gInvPi : EmlExpr := gE (gNeg (gL gPi))

theorem gInvPi_spec (x : ℂ) : gInvPi.evalC x = ((Real.pi⁻¹ : ℝ) : ℂ) := by
  rw [gInvPi, gE_spec (gNeg_spec (gL_spec (gPi_spec x) Real.pi_pos.le)), Real.exp_neg,
    Real.exp_log Real.pi_pos]

/-- **Absolute value, for all real a, with no log of 0 anywhere**: |a| = a · R / π. -/
def gAbs (s : EmlExpr) : EmlExpr := gMul (gMul s (gR s)) gInvPi

theorem gAbs_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gAbs s).evalC x = ((|a| : ℝ) : ℂ) := by
  rw [gAbs, gMul_spec (gMul_spec hs (gR_spec hs)) (gInvPi_spec x)]
  congr 1
  unfold sgnPi
  split_ifs with ha
  · rw [abs_of_nonneg ha, mul_inv_cancel_right₀ Real.pi_ne_zero]
  · rw [abs_of_neg (not_le.mp ha), mul_neg, neg_mul, mul_inv_cancel_right₀ Real.pi_ne_zero]

/-- **sin, for all real a**: sin a = cos(|a − π/2| + 2π), argument always > 0. -/
def gSin (s : EmlExpr) : EmlExpr :=
  gMul gHalf (gCos2 (gAdd (gAbs (gAdd s (gNeg (gMul gHalf gPi)))) (gMul (gNat 2) gPi)))

theorem gSin_spec {s : EmlExpr} {x : ℂ} {a : ℝ} (hs : s.evalC x = (a : ℂ)) :
    (gSin s).evalC x = ((Real.sin a : ℝ) : ℂ) := by
  have hpi := gPi_spec x
  have hP := gAdd_spec (gAbs_spec (gAdd_spec hs (gNeg_spec (gMul_spec (gHalf_spec x) hpi))))
    (gMul_spec (gNat_spec 2 x) hpi)
  have hpos : 0 < |a + -(1 / 2 * Real.pi)| + ((2 : ℕ) : ℝ) * Real.pi := by positivity
  rw [gSin, gMul_spec (gHalf_spec x) (gCos2_spec hP hpos)]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * Real.pi = 2 * Real.pi by norm_num, Real.cos_add_two_pi, Real.cos_abs,
    show a + -(1 / 2 * Real.pi) = a - Real.pi / 2 by ring, Real.cos_sub_pi_div_two]
  ring

/-! ## Part 6d — The complete gadget set -/

/-- All nine Richardson primitives as EML trees, each correct for every real input. -/
def theGadgets : Gadgets where
  rat := gFrac
  pi := gPi
  ln2 := gLn2
  add := gAdd
  mul := gMul
  sin := gSin
  exp := gE
  abs := gAbs
  rat_spec p q d x := gFrac_spec p q d x
  pi_spec x := gPi_spec x
  ln2_spec x := gLn2_spec x
  add_spec _ _ _ _ _ hs ht := gAdd_spec hs ht
  mul_spec _ _ _ _ _ hs ht := gMul_spec hs ht
  sin_spec _ _ _ hs := gSin_spec hs
  exp_spec _ _ _ hs := gE_spec hs
  abs_spec _ _ _ hs := gAbs_spec hs

/-- **Formerly the open problem, now proved**: a gadget set meeting the
    everywhere-on-ℝ specs exists. -/
theorem gadgets_exist : Nonempty Gadgets := ⟨theGadgets⟩

/-! ## Part 7a — The compiler is primitive recursive

Every gadget is a fixed tree template, so it is primitive recursive by composition
from `EmlExpr.app`. The compiler itself is obtained by course-of-values recursion on
Gödel numbers (`Primrec.nat_strong_rec`). -/

section Prim

theorem pI : Primrec fun a : EmlExpr => a := Primrec.id
theorem pL : Primrec₂ fun (a _ : EmlExpr) => a := Primrec₂.left
theorem pR : Primrec₂ fun (_ b : EmlExpr) => b := Primrec₂.right
theorem pC (c : EmlExpr) : Primrec fun _ : EmlExpr => c := Primrec.const c

theorem app_prim : Primrec₂ EmlExpr.app :=
  ((Primrec.of_equiv_symm (e := eE)).comp₂
    (Primrec.nat_add.comp₂
      (Primrec₂.natPair.comp₂ ((Primrec.of_equiv (e := eE)).comp₂ pL)
        ((Primrec.of_equiv (e := eE)).comp₂ pR))
      (Primrec₂.const 2 : Primrec₂ fun (_ _ : EmlExpr) => (2 : ℕ)))).of_eq
    fun a b => eE.symm_apply_apply (EmlExpr.app a b)

theorem gE_prim : Primrec gE := (app_prim.comp pI (pC .one)).of_eq fun _ => rfl
theorem gD_prim : Primrec₂ gD := (app_prim.comp₂ pL (gE_prim.comp₂ pR)).of_eq fun _ _ => rfl
theorem gL_prim : Primrec gL :=
  (app_prim.comp (pC .one) (gE_prim.comp (app_prim.comp (pC .one) pI))).of_eq fun _ => rfl
theorem gSub_prim : Primrec₂ gSub :=
  (app_prim.comp₂ (gL_prim.comp₂ pL) (gE_prim.comp₂ pR)).of_eq fun _ _ => rfl
theorem gAdd_prim : Primrec₂ gAdd :=
  (gD_prim.comp₂ pL (gSub_prim.comp₂ (gD_prim.comp₂ pL pL) pR)).of_eq fun _ _ => rfl
theorem gNeg_prim : Primrec gNeg :=
  (gD_prim.comp (pC gZero) (gAdd_prim.comp (pC .one) pI)).of_eq fun _ => rfl
theorem gPosMul_prim : Primrec₂ gPosMul :=
  (gE_prim.comp₂ (gAdd_prim.comp₂ (gL_prim.comp₂ pL) (gL_prim.comp₂ pR))).of_eq fun _ _ => rfl
theorem gMul_prim : Primrec₂ gMul :=
  (gAdd_prim.comp₂
    (gAdd_prim.comp₂ (gPosMul_prim.comp₂ (gE_prim.comp₂ pL) (gE_prim.comp₂ pR))
      (gNeg_prim.comp₂ (gPosMul_prim.comp₂ (gE_prim.comp₂ pL) (gD_prim.comp₂ pR pR))))
    (gAdd_prim.comp₂ (gNeg_prim.comp₂ (gPosMul_prim.comp₂ (gD_prim.comp₂ pL pL) (gE_prim.comp₂ pR)))
      (gPosMul_prim.comp₂ (gD_prim.comp₂ pL pL) (gD_prim.comp₂ pR pR)))).of_eq fun _ _ => rfl
theorem giP_prim : Primrec giP := (gE_prim.comp (gAdd_prim.comp gL_prim (pC gIH))).of_eq fun _ => rfl
theorem gmiP_prim : Primrec gmiP := (gE_prim.comp (gAdd_prim.comp gL_prim (pC gC))).of_eq fun _ => rfl
theorem gSig_prim : Primrec gSig :=
  (gE_prim.comp (gNeg_prim.comp (gL_prim.comp
    (gAdd_prim.comp (pC .one) (gE_prim.comp gNeg_prim))))).of_eq fun _ => rfl
theorem gW_prim : Primrec gW :=
  (gSub_prim.comp (giP_prim.comp gSig_prim) (pC (giP gHalf))).of_eq fun _ => rfl
theorem gU_prim : Primrec gU := (gAdd_prim.comp (pC .one) gW_prim).of_eq fun _ => rfl
theorem gZ_prim : Primrec gZ := (gNeg_prim.comp gU_prim).of_eq fun _ => rfl
theorem gT_prim : Primrec gT :=
  (gSub_prim.comp (gL_prim.comp gZ_prim) (gL_prim.comp gU_prim)).of_eq fun _ => rfl
theorem gR_prim : Primrec gR :=
  (gE_prim.comp (gSub_prim.comp (gL_prim.comp gT_prim) (pC gC))).of_eq fun _ => rfl
theorem gAbs_prim : Primrec gAbs :=
  (gMul_prim.comp (gMul_prim.comp pI gR_prim) (pC gInvPi)).of_eq fun _ => rfl
theorem gCos2_prim : Primrec gCos2 :=
  (gD_prim.comp giP_prim (gD_prim.comp (pC gZero)
    (gD_prim.comp gmiP_prim (pC (gNeg .one))))).of_eq fun _ => rfl
theorem gSin_prim : Primrec gSin :=
  (gMul_prim.comp (pC gHalf) (gCos2_prim.comp (gAdd_prim.comp
    (gAbs_prim.comp (gAdd_prim.comp pI (pC (gNeg (gMul gHalf gPi)))))
    (pC (gMul (gNat 2) gPi))))).of_eq fun _ => rfl

theorem gNat_iter (n : ℕ) : gNat n = (fun t => gAdd t .one)^[n] gZero := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem gNat_prim : Primrec gNat :=
  (Primrec.nat_iterate Primrec.id (Primrec.const gZero)
    (gAdd_prim.comp₂ Primrec₂.right (Primrec₂.const EmlExpr.one) :
      Primrec₂ fun (_ : ℕ) (t : EmlExpr) => gAdd t .one)).of_eq
    fun n => (gNat_iter n).symm

theorem gFrac_prim : Primrec (fun t : ℕ × ℕ × ℕ => gFrac t.1 t.2.1 t.2.2) := by
  have h1 : Primrec (fun t : ℕ × ℕ × ℕ => t.1) := Primrec.fst
  have h2 : Primrec (fun t : ℕ × ℕ × ℕ => t.2.1) := Primrec.fst.comp Primrec.snd
  have h3 : Primrec (fun t : ℕ × ℕ × ℕ => t.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  exact (gMul_prim.comp (gAdd_prim.comp (gNat_prim.comp h1) (gNeg_prim.comp (gNat_prim.comp h2)))
    (gE_prim.comp (gNeg_prim.comp (gL_prim.comp (gNat_prim.comp h3))))).of_eq fun _ => rfl

/-- One step of the course-of-values recursion: given the compiled trees of all codes
    `< n` (in `l`), produce the compiled tree of code `n`. The case split is done by
    list lookup at index `n − (n − 3) + (n − 3) % 6`. -/
def stepN (n : ℕ) (l : List EmlExpr) : EmlExpr :=
  [gPi, gLn2, EmlExpr.var,
    gFrac ((n - 3) / 6).unpair.1 ((n - 3) / 6).unpair.2.unpair.1 ((n - 3) / 6).unpair.2.unpair.2,
    gAdd (l.getD ((n - 3) / 6).unpair.1 .one) (l.getD ((n - 3) / 6).unpair.2 .one),
    gMul (l.getD ((n - 3) / 6).unpair.1 .one) (l.getD ((n - 3) / 6).unpair.2 .one),
    gSin (l.getD ((n - 3) / 6) .one),
    gE (l.getD ((n - 3) / 6) .one),
    gAbs (l.getD ((n - 3) / 6) .one)].getD (n - (n - 3) + (n - 3) % 6) .one

theorem stepN_prim : Primrec (fun p : ℕ × List EmlExpr => stepN p.1 p.2) := by
  have hn : Primrec (fun p : ℕ × List EmlExpr => p.1) := Primrec.fst
  have hl : Primrec (fun p : ℕ × List EmlExpr => p.2) := Primrec.snd
  have hm : Primrec (fun p : ℕ × List EmlExpr => p.1 - 3) :=
    Primrec.nat_sub.comp hn (Primrec.const 3)
  have hk : Primrec (fun p : ℕ × List EmlExpr => (p.1 - 3) / 6) :=
    Primrec.nat_div.comp hm (Primrec.const 6)
  have hk1 : Primrec (fun p : ℕ × List EmlExpr => ((p.1 - 3) / 6).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hk)
  have hk2 : Primrec (fun p : ℕ × List EmlExpr => ((p.1 - 3) / 6).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hk)
  have hk21 : Primrec (fun p : ℕ × List EmlExpr => ((p.1 - 3) / 6).unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hk2)
  have hk22 : Primrec (fun p : ℕ × List EmlExpr => ((p.1 - 3) / 6).unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hk2)
  have get : ∀ {f : ℕ × List EmlExpr → ℕ}, Primrec f →
      Primrec (fun p : ℕ × List EmlExpr => p.2.getD (f p) EmlExpr.one) :=
    fun hf => (Primrec.list_getD EmlExpr.one).comp hl hf
  have v3 := gFrac_prim.comp (Primrec.pair hk1 (Primrec.pair hk21 hk22))
  have v4 := gAdd_prim.comp (get hk1) (get hk2)
  have v5 := gMul_prim.comp (get hk1) (get hk2)
  have v6 := gSin_prim.comp (get hk)
  have v7 := gE_prim.comp (get hk)
  have v8 := gAbs_prim.comp (get hk)
  have L := Primrec.list_cons.comp (Primrec.const gPi) (Primrec.list_cons.comp
    (Primrec.const gLn2) (Primrec.list_cons.comp (Primrec.const EmlExpr.var)
    (Primrec.list_cons.comp v3 (Primrec.list_cons.comp v4 (Primrec.list_cons.comp v5
    (Primrec.list_cons.comp v6 (Primrec.list_cons.comp v7 (Primrec.list_cons.comp v8
    (Primrec.const ([] : List EmlExpr))))))))))
  have idx : Primrec (fun p : ℕ × List EmlExpr => p.1 - (p.1 - 3) + (p.1 - 3) % 6) :=
    Primrec.nat_add.comp (Primrec.nat_sub.comp hn hm) (Primrec.nat_mod.comp hm (Primrec.const 6))
  exact ((Primrec.list_getD EmlExpr.one).comp L idx).of_eq fun _ => rfl

/-- The compiler on Gödel numbers. -/
def compN (n : ℕ) : EmlExpr := compile theGadgets (decR n)

theorem getD_range_map {N i : ℕ} (h : i < N) :
    ((List.range N).map compN).getD i .one = compN i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem stepN_F : ∀ n, stepN n ((List.range n).map compN) = compN n
  | 0 => by show _ = compile theGadgets (decR 0); simp only [decR]; rfl
  | 1 => by show _ = compile theGadgets (decR 1); simp only [decR]; rfl
  | 2 => by show _ = compile theGadgets (decR 2); simp only [decR]; rfl
  | n + 3 => by
    have hl := Nat.unpair_left_le (n / 6)
    have hr := Nat.unpair_right_le (n / 6)
    have hd := Nat.div_le_self n 6
    have hi : ∀ i, i ≤ n / 6 → ((List.range (n + 3)).map compN).getD i .one = compN i :=
      fun i hi => getD_range_map (by omega)
    show stepN (n + 3) _ = compile theGadgets (decR (n + 3))
    rw [stepN, Nat.add_sub_cancel, show n + 3 - n + n % 6 = 3 + n % 6 by omega,
      hi _ hl, hi _ hr, hi _ le_rfl]
    simp only [decR]
    have h6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5)
      with h | h | h | h | h | h <;> (rw [h]) <;> rfl

theorem compN_prim : Primrec compN := by
  have hg : Primrec₂ (fun (_ : Unit) (l : List EmlExpr) => some (stepN l.length l)) :=
    (Primrec.option_some.comp (stepN_prim.comp
      (Primrec.pair (Primrec.list_length.comp Primrec.snd) Primrec.snd))).of_eq fun _ => rfl
  have := Primrec.nat_strong_rec (fun (_ : Unit) => compN) hg (fun _ n => by
    simp only [List.length_map, List.length_range, stepN_F])
  exact (this.comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

/-- **The compiler is primitive recursive** (w.r.t. the Gödel numberings of Part 1b). -/
theorem compile_prim : Primrec (compile theGadgets) :=
  (compN_prim.comp (Primrec.of_equiv (e := eR))).of_eq fun e => by
    show compile theGadgets (decR (encR e)) = _
    rw [decR_encR]

theorem compile_computable : Computable (compile theGadgets) := compile_prim.to_comp

end Prim

/-! ## Part 7 — Main results with the concrete compiler -/

/-- Every Richardson expression compiles to an EML tree with the same value at every real x. -/
theorem compile_theGadgets_correct (e : RExpr) (x : ℝ) :
    (compile theGadgets e).evalC x = ((e.eval x : ℝ) : ℂ) :=
  compile_correct theGadgets e x

/-- **Zero-equivalence of EML trees is undecidable**, assuming only Richardson's theorem. -/
theorem eml_zero_undecidable_final
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalC x = 0) :=
  eml_zero_undecidable theGadgets compile_computable richardson

/-- **Root existence for EML trees is undecidable**, assuming only Richardson's theorem. -/
theorem eml_root_undecidable_final
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalC x = 0) :=
  eml_root_undecidable theGadgets compile_computable richardson

/-! ## Part 8 — No `log 0` anywhere: the results do not depend on how log 0 is defined

Mathlib's `Complex.log 0 = 0` is a convention. `Safe x t` says that every `log`
node of `t` receives a nonzero argument at `x`. Every compiled tree is safe at every
real `x`, so its value is the same under any convention for `log 0`: undefined
(`evalO`, partial semantics) or any fixed value `c` (`evalJ c`). The undecidability
theorems are restated for all of these semantics. -/

/-- Every `log` node of `t` receives a nonzero argument at `x`. -/
def Safe (x : ℂ) : EmlExpr → Prop
  | .one => True
  | .var => True
  | .app l r => Safe x l ∧ Safe x r ∧ r.evalC x ≠ 0

section Safety

variable {x : ℂ}

theorem safe_app {l r : EmlExpr} (hl : Safe x l) (hr : Safe x r) (h : r.evalC x ≠ 0) :
    Safe x (.app l r) := by
  simp only [Safe]; exact ⟨hl, hr, h⟩

theorem safe_one : Safe x .one := by simp only [Safe]
theorem safe_var : Safe x .var := by simp only [Safe]

theorem safe_gE {s : EmlExpr} (hs : Safe x s) : Safe x (gE s) :=
  safe_app hs safe_one (by simp [EmlExpr.evalC])

theorem safe_gD {s t : EmlExpr} (hs : Safe x s) (ht : Safe x t) : Safe x (gD s t) :=
  safe_app hs (safe_gE ht) (by rw [gE_C]; exact Complex.exp_ne_zero _)

theorem safe_gL {s : EmlExpr} (hs : Safe x s) (h : s.evalC x ≠ 0) : Safe x (gL s) :=
  safe_app safe_one (safe_gE (safe_app safe_one hs h)) (by rw [gE_C]; exact Complex.exp_ne_zero _)

theorem safe_gSub {s t : EmlExpr} (hs : Safe x s) (h : s.evalC x ≠ 0) (ht : Safe x t) :
    Safe x (gSub s t) :=
  safe_app (safe_gL hs h) (safe_gE ht) (by rw [gE_C]; exact Complex.exp_ne_zero _)

theorem safe_gAdd {s t : EmlExpr} {a : ℝ} (hs : Safe x s) (ht : Safe x t)
    (hsv : s.evalC x = (a : ℂ)) : Safe x (gAdd s t) := by
  have hp : 0 < Real.exp a - a := by linarith [Real.add_one_le_exp a]
  exact safe_gD hs (safe_gSub (safe_gD hs hs) (by rw [gD_spec hsv hsv]; exact_mod_cast hp.ne') ht)

theorem safe_gZero : Safe x gZero := safe_gL safe_one (by simp [EmlExpr.evalC])

theorem safe_gNeg {t : EmlExpr} (ht : Safe x t) : Safe x (gNeg t) :=
  safe_gD safe_gZero (safe_gAdd safe_one ht (one_eval x))

theorem safe_gPosMul {s t : EmlExpr} {p q : ℝ} (hs : Safe x s) (ht : Safe x t)
    (hsv : s.evalC x = (p : ℂ)) (htv : t.evalC x = (q : ℂ)) (hp : 0 < p) (hq : 0 < q) :
    Safe x (gPosMul s t) :=
  safe_gE (safe_gAdd (safe_gL hs (by rw [hsv]; exact_mod_cast hp.ne'))
    (safe_gL ht (by rw [htv]; exact_mod_cast hq.ne')) (gL_spec hsv hp.le))

theorem safe_gMul {s t : EmlExpr} {a b : ℝ} (hs : Safe x s) (ht : Safe x t)
    (hsv : s.evalC x = (a : ℂ)) (htv : t.evalC x = (b : ℂ)) : Safe x (gMul s t) := by
  have pa1 : 0 < Real.exp a := Real.exp_pos a
  have pb1 : 0 < Real.exp b := Real.exp_pos b
  have pa2 : 0 < Real.exp a - a := by linarith [Real.add_one_le_exp a]
  have pb2 : 0 < Real.exp b - b := by linarith [Real.add_one_le_exp b]
  have hP1 := gE_spec hsv
  have hQ1 := gE_spec htv
  have hP2 := gD_spec hsv hsv
  have hQ2 := gD_spec htv htv
  have sP1 := safe_gE hs
  have sQ1 := safe_gE ht
  have sP2 := safe_gD hs hs
  have sQ2 := safe_gD ht ht
  exact safe_gAdd
    (safe_gAdd (safe_gPosMul sP1 sQ1 hP1 hQ1 pa1 pb1)
      (safe_gNeg (safe_gPosMul sP1 sQ2 hP1 hQ2 pa1 pb2)) (gPosMul_spec hP1 hQ1 pa1 pb1))
    (safe_gAdd (safe_gNeg (safe_gPosMul sP2 sQ1 hP2 hQ1 pa2 pb1))
      (safe_gPosMul sP2 sQ2 hP2 hQ2 pa2 pb2) (gNeg_spec (gPosMul_spec hP2 hQ1 pa2 pb1)))
    (gAdd_spec (gPosMul_spec hP1 hQ1 pa1 pb1) (gNeg_spec (gPosMul_spec hP1 hQ2 pa1 pb2)))

theorem safe_gHalf : Safe x gHalf :=
  safe_gE (safe_gNeg (safe_gL (safe_gAdd safe_one safe_one (one_eval x))
    (by rw [gAdd_spec (one_eval x) (one_eval x)]; norm_num)))

theorem safe_gNat : ∀ n, Safe x (gNat n)
  | 0 => safe_gZero
  | n + 1 => safe_gAdd (safe_gNat n) safe_one (gNat_spec n x)

theorem safe_gFrac (p q d : ℕ) : Safe x (gFrac p q d) := by
  have hden : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  exact safe_gMul (safe_gAdd (safe_gNat p) (safe_gNeg (safe_gNat q)) (gNat_spec p x))
    (safe_gE (safe_gNeg (safe_gL (safe_gNat (d + 1)) (by rw [gNat_spec]; exact_mod_cast hden.ne'))))
    (gAdd_spec (gNat_spec p x) (gNeg_spec (gNat_spec q x)))
    (gE_spec (gNeg_spec (gL_spec (gNat_spec (d + 1) x) hden.le)))

theorem safe_gLn2 : Safe x gLn2 := safe_gL (safe_gNat 2) (by rw [gNat_spec]; norm_num)

theorem safe_gV : Safe x gV := safe_gL (safe_gNeg safe_one) (by rw [gNeg_spec (one_eval x)]; norm_num)

theorem safe_gC : Safe x gC :=
  safe_gE (safe_gAdd (safe_gL safe_gHalf (by rw [gHalf_spec]; norm_num))
    (safe_gL safe_gV (by rw [gV_spec]; exact hV0)) (gL_spec (gHalf_spec x) (by norm_num)))

theorem safe_gPi : Safe x gPi :=
  safe_gE (safe_gSub (safe_gL safe_gV (by rw [gV_spec]; exact hV0)) (gLV_ne x) safe_gC)

theorem safe_gIH : Safe x gIH := safe_gNeg safe_gC

theorem safe_giP {P : EmlExpr} {p : ℝ} (hPs : Safe x P) (hP : P.evalC x = (p : ℂ)) (hp : 0 < p) :
    Safe x (giP P) :=
  safe_gE (safe_gAdd (safe_gL hPs (by rw [hP]; exact_mod_cast hp.ne')) safe_gIH (gL_spec hP hp.le))

theorem safe_gmiP {P : EmlExpr} {p : ℝ} (hPs : Safe x P) (hP : P.evalC x = (p : ℂ)) (hp : 0 < p) :
    Safe x (gmiP P) :=
  safe_gE (safe_gAdd (safe_gL hPs (by rw [hP]; exact_mod_cast hp.ne')) safe_gC (gL_spec hP hp.le))

theorem safe_gCos2 {P : EmlExpr} {p : ℝ} (hPs : Safe x P) (hP : P.evalC x = (p : ℂ)) (hp : 0 < p) :
    Safe x (gCos2 P) :=
  safe_gD (safe_giP hPs hP hp) (safe_gD safe_gZero (safe_gD (safe_gmiP hPs hP hp) (safe_gNeg safe_one)))

theorem safe_gSig {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gSig s) := by
  have hpos : 0 < 1 + Real.exp (-a) := by positivity
  exact safe_gE (safe_gNeg (safe_gL (safe_gAdd safe_one (safe_gE (safe_gNeg hs)) (one_eval x))
    (by rw [gAdd_spec (one_eval x) (gE_spec (gNeg_spec hsv))]; exact_mod_cast hpos.ne')))

theorem safe_gW {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gW s) := by
  have hpos : 0 < 1 + Real.exp (-a) := by positivity
  exact safe_gSub (safe_giP (safe_gSig hs hsv) (gSig_spec hsv) (inv_pos.mpr hpos))
    (giP_sig_ne hsv) (safe_giP safe_gHalf (gHalf_spec x) (by norm_num))

theorem safe_gU {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gU s) := safe_gAdd safe_one (safe_gW hs hsv) (one_eval x)

theorem safe_gZ {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gZ s) := safe_gNeg (safe_gU hs hsv)

theorem safe_gT {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gT s) :=
  safe_gSub (safe_gL (safe_gZ hs hsv) (by rw [gZ_spec hsv]; exact neg_ne_zero.mpr (u_ne _)))
    (gLZ_ne hsv) (safe_gL (safe_gU hs hsv) (by rw [gU_spec hsv]; exact u_ne _))

theorem safe_gR {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gR s) :=
  safe_gE (safe_gSub (safe_gL (safe_gT hs hsv) (gT_ne hsv)) (gLT_ne hsv) safe_gC)

theorem safe_gInvPi : Safe x gInvPi :=
  safe_gE (safe_gNeg (safe_gL safe_gPi (by rw [gPi_spec]; exact_mod_cast Real.pi_ne_zero)))

theorem safe_gAbs {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gAbs s) :=
  safe_gMul (safe_gMul hs (safe_gR hs hsv) hsv (gR_spec hsv)) safe_gInvPi
    (gMul_spec hsv (gR_spec hsv)) (gInvPi_spec x)

theorem safe_gSin {s : EmlExpr} {a : ℝ} (hs : Safe x s) (hsv : s.evalC x = (a : ℂ)) :
    Safe x (gSin s) := by
  have hpi := gPi_spec x
  have hA := gAdd_spec hsv (gNeg_spec (gMul_spec (gHalf_spec x) hpi))
  have hP := gAdd_spec (gAbs_spec hA) (gMul_spec (gNat_spec 2 x) hpi)
  have hpos : 0 < |a + -(1 / 2 * Real.pi)| + ((2 : ℕ) : ℝ) * Real.pi := by positivity
  have sA := safe_gAdd hs (safe_gNeg (safe_gMul safe_gHalf safe_gPi (gHalf_spec x) hpi)) hsv
  have sP := safe_gAdd (safe_gAbs sA hA) (safe_gMul (safe_gNat 2) safe_gPi (gNat_spec 2 x) hpi)
    (gAbs_spec hA)
  exact safe_gMul safe_gHalf (safe_gCos2 sP hP hpos) (gHalf_spec x) (gCos2_spec hP hpos)

end Safety

/-- **No compiled tree ever takes log 0**, at any real input. -/
theorem compile_safe (x : ℝ) : ∀ e : RExpr, Safe (x : ℂ) (compile theGadgets e)
  | .rat p q d => safe_gFrac p q d
  | .pi => safe_gPi
  | .ln2 => safe_gLn2
  | .var => safe_var
  | .add a b => safe_gAdd (compile_safe x a) (compile_safe x b) (compile_correct _ a x)
  | .mul a b => safe_gMul (compile_safe x a) (compile_safe x b) (compile_correct _ a x)
      (compile_correct _ b x)
  | .sin a => safe_gSin (compile_safe x a) (compile_correct _ a x)
  | .exp a => safe_gE (compile_safe x a)
  | .abs a => safe_gAbs (compile_safe x a) (compile_correct _ a x)

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
/-- Semantics with an arbitrary value `c` for log 0. -/
noncomputable def EmlExpr.evalJ (c x : ℂ) : EmlExpr → ℂ
  | .one => 1
  | .var => x
  | .app l r => Complex.exp (l.evalJ c x) -
      (if r.evalJ c x = 0 then c else Complex.log (r.evalJ c x))

theorem evalO_of_safe {x : ℂ} : ∀ t : EmlExpr, Safe x t → t.evalO x = some (t.evalC x)
  | .one, _ => rfl
  | .var, _ => rfl
  | .app l r, h => by
    simp only [Safe] at h
    obtain ⟨hl, hr, h0⟩ := h
    simp [EmlExpr.evalO, evalO_of_safe l hl, evalO_of_safe r hr, h0, EmlExpr.evalC, ceml]

theorem evalJ_of_safe {x : ℂ} (c : ℂ) : ∀ t : EmlExpr, Safe x t → t.evalJ c x = t.evalC x
  | .one, _ => rfl
  | .var, _ => rfl
  | .app l r, h => by
    simp only [Safe] at h
    obtain ⟨hl, hr, h0⟩ := h
    simp [EmlExpr.evalJ, evalJ_of_safe c l hl, evalJ_of_safe c r hr, h0, EmlExpr.evalC, ceml]

theorem compile_evalO (e : RExpr) (x : ℝ) :
    (compile theGadgets e).evalO x = some ((e.eval x : ℝ) : ℂ) := by
  rw [evalO_of_safe _ (compile_safe x e), compile_correct]

theorem compile_evalJ (c : ℂ) (e : RExpr) (x : ℝ) :
    (compile theGadgets e).evalJ c x = ((e.eval x : ℝ) : ℂ) := by
  rw [evalJ_of_safe c _ (compile_safe x e), compile_correct]

/-- Zero-equivalence is undecidable with log 0 **undefined**. -/
theorem eml_zero_undecidable_partial
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalO x = some 0) := fun h =>
  richardson (ComputablePred.computable_of_manyOneReducible
    ⟨compile theGadgets, compile_computable, fun e => by
      simp only [compile_evalO, Option.some.injEq, Complex.ofReal_eq_zero]⟩ h)

/-- Root existence is undecidable with log 0 **undefined**. -/
theorem eml_root_undecidable_partial
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalO x = some 0) := fun h =>
  richardson (ComputablePred.computable_of_manyOneReducible
    ⟨compile theGadgets, compile_computable, fun e => by
      simp only [compile_evalO, Option.some.injEq, Complex.ofReal_eq_zero]⟩ h)

/-- Zero-equivalence is undecidable for **every** choice of value for log 0. -/
theorem eml_zero_undecidable_any (c : ℂ)
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∀ x : ℝ, t.evalJ c x = 0) := fun h =>
  richardson (ComputablePred.computable_of_manyOneReducible
    ⟨compile theGadgets, compile_computable, fun e => by
      simp only [compile_evalJ, Complex.ofReal_eq_zero]⟩ h)

/-- Root existence is undecidable for **every** choice of value for log 0. -/
theorem eml_root_undecidable_any (c : ℂ)
    (richardson : ¬ ComputablePred (fun e : RExpr => ∃ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, t.evalJ c x = 0) := fun h =>
  richardson (ComputablePred.computable_of_manyOneReducible
    ⟨compile theGadgets, compile_computable, fun e => by
      simp only [compile_evalJ, Complex.ofReal_eq_zero]⟩ h)

/-! ## Part 9 — The statement `compiler_exists` of Challenge.lean -/

/-- **The reduction.** There is a computable translation of Richardson expressions into
    EML trees that preserves the value at every real `x` (0 and negative values included)
    and never takes `log 0` at any real input. -/
theorem compiler_exists :
    ∃ f : RExpr → EmlExpr, Computable f ∧
      ∀ (e : RExpr) (x : ℝ), (f e).evalC x = ((e.eval x : ℝ) : ℂ) ∧ Safe (x : ℂ) (f e) :=
  ⟨compile theGadgets, compile_computable, fun e x => ⟨compile_correct theGadgets e x, compile_safe x e⟩⟩


/-! ## Part 10 — More undecidable problems

Three further decision problems for EML trees, each reduced from Richardson's
zero-equivalence problem with the same concrete compiler:

* equivalence: do two EML trees agree at every real `x`?
* negativity: does a tree take a negative real value at some real `x`?
* constancy: is a tree constant on ℝ?

Negativity uses the complement of the zero problem (`ComputablePred.not`); constancy uses
the continuity of Richardson expressions. -/

/-- Every Richardson expression denotes a continuous function of `x`. -/
theorem eval_continuous : ∀ e : RExpr, Continuous (fun x : ℝ => e.eval x)
  | .rat p q d => by simp only [RExpr.eval]; exact continuous_const
  | .pi => by simp only [RExpr.eval]; exact continuous_const
  | .ln2 => by simp only [RExpr.eval]; exact continuous_const
  | .var => by simp only [RExpr.eval]; exact continuous_id
  | .add a b => by simp only [RExpr.eval]; exact (eval_continuous a).add (eval_continuous b)
  | .mul a b => by simp only [RExpr.eval]; exact (eval_continuous a).mul (eval_continuous b)
  | .sin a => by simp only [RExpr.eval]; exact Real.continuous_sin.comp (eval_continuous a)
  | .exp a => by simp only [RExpr.eval]; exact Real.continuous_exp.comp (eval_continuous a)
  | .abs a => by simp only [RExpr.eval]; exact continuous_abs.comp (eval_continuous a)

/-- `e ≡ 0` iff the compiled tree of `e` agrees everywhere with the compiled tree of 0. -/
theorem equivPb_iff (e : RExpr) :
    (∀ x : ℝ, e.eval x = 0) ↔
      ∀ x : ℝ, (compile theGadgets e).evalC x = (compile theGadgets (.rat 0 0 0)).evalC x := by
  simp [compile_correct, RExpr.eval]

/-- `e ≢ 0` iff the compiled tree of `-|e|` is negative somewhere. -/
theorem negPb_iff (e : RExpr) :
    (¬ ∀ x : ℝ, e.eval x = 0) ↔
      ∃ x : ℝ, ∃ r : ℝ, r < 0 ∧
        (compile theGadgets (.mul (.rat 0 1 0) (.abs e))).evalC x = r := by
  simp only [compile_correct, RExpr.eval, Complex.ofReal_inj]
  constructor
  · intro h
    push_neg at h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, _, by norm_num [hx], rfl⟩
  · rintro ⟨x, r, hr, hx⟩ h
    rw [h x] at hx
    norm_num at hx
    linarith

/-- `e ≡ 0` iff the compiled tree of `x · e` is constant. The converse direction uses
    continuity: `x · e(x) = 0` forces `e = 0` off 0, hence everywhere. -/
theorem constPb_iff (e : RExpr) :
    (∀ x : ℝ, e.eval x = 0) ↔
      ∃ c : ℂ, ∀ x : ℝ, (compile theGadgets (.mul .var e)).evalC x = c := by
  simp only [compile_correct, RExpr.eval]
  constructor
  · intro h
    exact ⟨0, fun x => by simp [h x]⟩
  · rintro ⟨c, hc⟩
    have h0 : c = 0 := by simpa using (hc 0).symm
    have hne : ∀ x : ℝ, x ≠ 0 → e.eval x = 0 := fun x hx => by
      have := hc x
      rw [h0, Complex.ofReal_eq_zero, mul_eq_zero] at this
      exact this.resolve_left hx
    have heq : (fun x => e.eval x) = fun _ => (0 : ℝ) :=
      Continuous.ext_on (dense_compl_singleton (0 : ℝ)) (eval_continuous e) continuous_const
        (fun x hx => hne x (by simpa using hx))
    exact fun x => congrFun heq x

theorem negF_computable :
    Computable (fun e : RExpr => compile theGadgets (.mul (.rat 0 1 0) (.abs e))) :=
  ((gMul_prim.comp (Primrec.const (compile theGadgets (.rat 0 1 0)))
    (gAbs_prim.comp compile_prim)).to_comp).of_eq fun _ => rfl

theorem constF_computable :
    Computable (fun e : RExpr => compile theGadgets (.mul .var e)) :=
  ((gMul_prim.comp (Primrec.const EmlExpr.var) compile_prim).to_comp).of_eq fun _ => rfl

/-- **Equivalence of two EML trees is undecidable**, assuming Richardson's theorem. -/
theorem eml_equiv_undecidable
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun p : EmlExpr × EmlExpr => ∀ x : ℝ, p.1.evalC x = p.2.evalC x) :=
  fun h => richardson (ComputablePred.computable_of_manyOneReducible
    ⟨fun e => (compile theGadgets e, compile theGadgets (.rat 0 0 0)),
      compile_computable.pair (Computable.const _), equivPb_iff⟩ h)

/-- **Negativity of an EML tree is undecidable**: whether it takes a negative real value
    at some real `x`, assuming Richardson's theorem. -/
theorem eml_neg_undecidable
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ x : ℝ, ∃ r : ℝ, r < 0 ∧ t.evalC x = r) := fun h => by
  have h1 : ComputablePred (fun e : RExpr => ¬ ∀ x : ℝ, e.eval x = 0) :=
    ComputablePred.computable_of_manyOneReducible ⟨_, negF_computable, negPb_iff⟩ h
  exact richardson (by simpa only [not_not] using h1.not)

/-- **Constancy of an EML tree on ℝ is undecidable**, assuming Richardson's theorem. -/
theorem eml_const_undecidable
    (richardson : ¬ ComputablePred (fun e : RExpr => ∀ x : ℝ, e.eval x = 0)) :
    ¬ ComputablePred (fun t : EmlExpr => ∃ c : ℂ, ∀ x : ℝ, t.evalC x = c) :=
  fun h => richardson (ComputablePred.computable_of_manyOneReducible
    ⟨_, constF_computable, constPb_iff⟩ h)

end EmlRichardson

end

#print axioms EmlRichardson.compiler_exists
#print axioms EmlRichardson.gadgets_exist
#print axioms EmlRichardson.compile_computable
#print axioms EmlRichardson.eml_zero_undecidable_final
#print axioms EmlRichardson.eml_root_undecidable_final
#print axioms EmlRichardson.compile_safe
#print axioms EmlRichardson.eml_zero_undecidable_partial
#print axioms EmlRichardson.eml_root_undecidable_partial
#print axioms EmlRichardson.eml_zero_undecidable_any
#print axioms EmlRichardson.eml_root_undecidable_any
#print axioms EmlRichardson.eml_equiv_undecidable
#print axioms EmlRichardson.eml_neg_undecidable
#print axioms EmlRichardson.eml_const_undecidable
