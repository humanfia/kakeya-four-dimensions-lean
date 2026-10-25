import Submission.Obl.k4_raw_critical_segment_forests.ParentRemainder
import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport

/-!
# Nested normalization, over the o153 problem records

Paper, Lemma 2.13 (`lem:normalization`) with its explicit lifting, as used in
Proposition 4.3(2): a valid problem `G` is normalized through given known parent
atlases at depth `r`; every true terminal atlas of the remainder lifts to a true
terminal atlas of `G` nested in the parents, with time partitions concatenated and
Jacobians multiplied.

`NestedNormalization` is stated over the accepted o153 records (`Data`, `Atlas`,
`Atlas.TrueAt`, `Atlas.KnownAt`), which the raw forest assembly uses.  It follows
from `ParentRemainderConstruction` (normalization through given parents, in o183's
`Remainder` terms) and o183's terminal lifting.
-/

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

/-- o183's problem record. -/
abbrev LData := Submission.Obl.k4_native_finite_terminal_atlas_lift.Data
/-- o183's atlas record (with its own slack). -/
abbrev LAtlas := Submission.Obl.k4_native_finite_terminal_atlas_lift.Atlas

/-- The o183 record of an o153 problem. -/
def toL (p : Data) : LData :=
  ⟨p.N, p.K, p.L, p.d, p.S, p.η, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

/-- The o153 record of an o183 problem. -/
def ofL (q : LData) : Data :=
  ⟨q.N, q.K, q.L, q.d, q.S, q.η, q.W, q.ω, q.ν, q.E, q.P, q.B, q.f, q.g, q.G⟩

theorem valid_toL_iff (p : Data) : Valid p ↔ (toL p).Valid := Iff.rfl

theorem valid_ofL_iff (q : LData) : Valid (ofL q) ↔ q.Valid := Iff.rfl

/-- An o153 atlas with a chosen slack, as an o183 atlas. -/
def atlasToL {p : Data} {k : ℕ} (a : Atlas p k) (κ : ℝ) : LAtlas (toL p) k :=
  ⟨κ, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F⟩

/-- An o183 atlas as an o153 atlas (with empty lists). -/
def atlasOfL {q : LData} {k : ℕ} (a : LAtlas q k) : Atlas (ofL q) k :=
  ⟨a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F, fun _ _ => ∅⟩

theorem trueAt_atlasToL {p : Data} {k : ℕ} {a : Atlas p k} {M D : ℕ} {κ : ℝ}
    (h : a.TrueAt M D κ) : (atlasToL a κ).TrueAt M D (toL p).L := h

theorem trueAt_atlasOfL {q : LData} {k : ℕ} {a : LAtlas q k} {M D : ℕ}
    (h : a.TrueAt M D q.L) : (atlasOfL a).TrueAt M D a.κ := h

/-- Move an o153 atlas to an equal sample index, keeping all fields. -/
def castIdx {p : Data} {k k' : ℕ} (hk : k = k') (a : Atlas p k) : Atlas p k' :=
  ⟨a.T, a.C, fun b => Fin.cast (by rw [hk]) (a.γ b), a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
    fun γ o => a.lst (Fin.cast (by rw [hk]) γ) o⟩

theorem castIdx_trueAt {p : Data} {k k' : ℕ} (hk : k = k') {a : Atlas p k}
    {M D : ℕ} {κ : ℝ} (h : a.TrueAt M D κ) : (castIdx hk a).TrueAt M D κ := by
  subst hk
  exact h

@[simp] theorem castIdx_γ_val {p : Data} {k k' : ℕ} (hk : k = k') (a : Atlas p k)
    (b : Fin a.C) : (((castIdx hk a).γ b : Fin (p.W k')) : ℕ) = (a.γ b : ℕ) := rfl

/-- Charts of `child` lie in the charts of `par` named by `pmap`: the same world,
nested assignments and incidence selections, nested time blocks. -/
def NestedIn {G : Data} {k : ℕ} (child par : Atlas G k) (pmap : Fin child.C → Fin par.C) :
    Prop :=
  ∀ b, child.γ b = par.γ (pmap b) ∧ child.A b ⊆ par.A (pmap b) ∧
    child.F b ⊆ par.F (pmap b) ∧
    ((par.j (pmap b) : ℕ) : ℝ) / (2 : ℝ) ^ par.T ≤ ((child.j b : ℕ) : ℝ) / (2 : ℝ) ^ child.T ∧
    (((child.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ child.T ≤
      (((par.j (pmap b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ par.T

/-- An explicitly given known parent atlas: slack `κ`, time partition bounded by the
format, labels known by the terminal observation of `G` (`Atlas.KnownAt`, using the
atlas' own lists). -/
def KnownParent (G : Data) (M D : ℕ) (r ε κ : ℝ) {k : ℕ} (a : Atlas G k) : Prop :=
  1 ≤ κ ∧ G.K k ≤ κ ∧ κ ≤ G.N k ^ ε ∧ (2 : ℝ) ^ a.T ≤ G.N k ^ M ∧ a.KnownAt M D κ r

/-- **Nested normalization.**  For a valid `G`, a depth `0 ≤ r < G.L`, a fixed format
and known parents along a subsequence with vanishing slack exponents, there is a valid
remainder of length `G.L - r` (same `d, S, η`) along a further subsequence `ψ`, whose
true terminal atlases lift to true terminal atlases of `G` nested in the parents, with
time partitions concatenated and Jacobians multiplied.  The lifting format is fixed
before the output tolerance. -/
def NestedNormalization : Prop :=
  ∀ (G : Data), Valid G → ∀ r : ℝ, 0 ≤ r → r < G.L →
  ∀ (M D : ℕ) (φ : ℕ → ℕ) (ε κ : ℕ → ℝ) (par : (n : ℕ) → Atlas G (φ n)),
    StrictMono φ → (∀ n, 0 < ε n) → Tendsto ε atTop (nhds 0) →
    (∀ n, KnownParent G M D r (ε n) (κ n) (par n)) →
    ∃ (q : Data) (ψ : ℕ → ℕ), Valid q ∧ q.L = G.L - r ∧ q.d = G.d ∧ q.S = G.S ∧
      q.η = G.η ∧ StrictMono ψ ∧ (∀ n, q.N n = G.N (φ (ψ n))) ∧
      ∀ M' D' : ℕ, ∃ M'' D'' : ℕ, ∀ e : ℝ, 0 < e → ∃ e' : ℝ, 0 < e' ∧
        ∀ᶠ n in atTop, ∀ (κ' : ℝ) (a : Atlas q n), 1 ≤ κ' → q.K n ≤ κ' →
          κ' ≤ q.N n ^ e' → a.TrueAt M' D' κ' →
          ∃ (κ'' : ℝ) (c : Atlas G (φ (ψ n))) (pmap : Fin c.C → Fin (par (ψ n)).C)
            (cmap : Fin c.C → Fin a.C),
            1 ≤ κ'' ∧ G.K (φ (ψ n)) ≤ κ'' ∧ κ'' ≤ G.N (φ (ψ n)) ^ e ∧
            c.T = (par (ψ n)).T + a.T ∧ c.TrueAt M'' D'' κ'' ∧
            NestedIn c (par (ψ n)) pmap ∧
            ∀ b, |Matrix.det (c.Q b)| * (4 : ℝ) ^ c.T =
              (|Matrix.det ((par (ψ n)).Q (pmap b))| * (4 : ℝ) ^ (par (ψ n)).T) *
                (|Matrix.det (a.Q (cmap b))| * (4 : ℝ) ^ a.T)

end Submission.Obl.k4_raw_critical_segment_forests
