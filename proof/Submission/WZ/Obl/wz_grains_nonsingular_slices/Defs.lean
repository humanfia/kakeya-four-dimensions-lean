-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Basic

/-!
# Twisted coordinates and grain fibres

`twist f p = p 0 + f (p 2) * p 1` is the twisted coordinate, and `ofTwist f u y z` is the
point with twisted coordinate `u`, second coordinate `y` and height `z`.  For fixed `(u, z)`
the points `ofTwist f u y z` form the horizontal *grain* line through twisted position `u`
at height `z`; `grainFib f A u z` is the set of `y` for which that point lies in `A`.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The twisted coordinate. -/
def twist (f : ℝ → ℝ) (p : Space) : ℝ := p 0 + f (p 2) * p 1

/-- The point with twisted coordinate `u`, second coordinate `y`, and height `z`. -/
noncomputable def ofTwist (f : ℝ → ℝ) (u y z : ℝ) : Space :=
  WithLp.toLp 2 ![u - f z * y, y, z]

/-- The grain fibre of `A` at twisted position `u` and height `z`. -/
def grainFib (f : ℝ → ℝ) (A : Set Space) (u z : ℝ) : Set ℝ := {y | ofTwist f u y z ∈ A}

@[simp] lemma ofTwist_zero (f : ℝ → ℝ) (u y z : ℝ) : ofTwist f u y z 0 = u - f z * y := rfl
@[simp] lemma ofTwist_one (f : ℝ → ℝ) (u y z : ℝ) : ofTwist f u y z 1 = y := rfl
@[simp] lemma ofTwist_two (f : ℝ → ℝ) (u y z : ℝ) : ofTwist f u y z 2 = z := rfl

@[simp] lemma twist_ofTwist (f : ℝ → ℝ) (u y z : ℝ) : twist f (ofTwist f u y z) = u := by
  simp [twist]

lemma ofTwist_twist (f : ℝ → ℝ) (p : Space) : ofTwist f (twist f p) (p 1) (p 2) = p := by
  ext i
  fin_cases i <;> simp [ofTwist, twist]

lemma mem_grainFib {f : ℝ → ℝ} {A : Set Space} {u z y : ℝ} :
    y ∈ grainFib f A u z ↔ ofTwist f u y z ∈ A := Iff.rfl

lemma mem_PS_iff {f : ℝ → ℝ} {A : Set Space} {u z : ℝ} :
    u ∈ PS f A z ↔ (grainFib f A u z).Nonempty := by
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨hu, hz⟩ := Prod.mk.inj he
    refine ⟨p 1, ?_⟩
    rw [mem_grainFib, ← hu, ← hz]
    simpa [twist] using (ofTwist_twist f p).symm ▸ hp
  · rintro ⟨y, hy⟩
    exact ⟨ofTwist f u y z, hy, by simp⟩

lemma grainFib_mono {f : ℝ → ℝ} {A B : Set Space} (h : A ⊆ B) (u z : ℝ) :
    grainFib f A u z ⊆ grainFib f B u z := fun _ hy => h hy

lemma continuous_ofTwist {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun t : ℝ × ℝ × ℝ => ofTwist f t.1 t.2.1 t.2.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst.sub ((hf.comp (continuous_snd.comp continuous_snd)).mul
      (continuous_fst.comp continuous_snd))
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_snd

lemma continuous_twist {f : ℝ → ℝ} (hf : Continuous f) : Continuous (twist f) := by
  unfold twist
  fun_prop

end WangZahlLot.Obl.wz_grains_nonsingular_slices

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- Basic properties of a shaded tube family (no distinctness, no mass). -/
structure Family (δ : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop where
  unit : ∀ i, ‖v i‖ = 1
  ball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1
  meas : ∀ i, MeasurableSet (Y i)
  sub : ∀ i, Y i ⊆ Tube δ (x i) (v i)

/-- The global grains hypothesis: AD horizontal twisted slices. -/
def GlobalGrains (σ η δ : ℝ) (f : ℝ → ℝ) (E : Set Space) : Prop :=
  ∀ z ∈ Icc (-1 : ℝ) 1, AD δ (1 - σ) (δ ^ (-η)) (PS f E z)

/-- The local grains hypothesis for a plane map `P`. -/
def LocalGrains (σ η δ : ℝ) (P : Space → Space) (E : Set Space) : Prop :=
  ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ E,
    AD ρ (1 - σ) (δ ^ (-η)) ((fun q : Space => inner ℝ (P p) q) '' (E ∩ ball p (Real.sqrt ρ)))

/-- `y` is a locally full point of `F ⊆ ℝ` at scale `ℓ` with density `κ`. -/
def LocFull (F : Set ℝ) (ℓ κ : ℝ) (y : ℝ) : Prop :=
  ENNReal.ofReal (κ * ℓ) ≤ volume (F ∩ Icc (y - ℓ / 2) (y + ℓ / 2))

/-- Points lying on grains whose fibre has measure at least `lam`. -/
def FullPart (f : ℝ → ℝ) (E : Set Space) (lam : ℝ) : Set Space :=
  {q | ENNReal.ofReal lam ≤ volume (grainFib f E (twist f q) (q 2))}

end WangZahlLot.Obl.wz_grains_nonsingular_slices
