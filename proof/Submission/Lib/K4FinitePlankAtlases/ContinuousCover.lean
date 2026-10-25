import Submission.Lib.K4FinitePlankAtlases.ScaleDensity
import Submission.Lib.K4FinitePlankAtlases.Greedy
import Submission.Lib.K4FinitePlankAtlases.Assignments

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/ContinuousCover.lean.
Uses the accepted K4ContinuousPlanks finite-approximation and weighted APIs.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Lib.K4ContinuousPlanks

/-- The full-time rectangular test is determined by its two endpoints. -/
theorem fullTracePlank_iff_endpoints (b u c w e₁ e₂ : Plane) (a β : ℝ) :
    InFullTracePlank b u c w e₁ e₂ a β ↔
      (|inner ℝ (b - c) e₁| ≤ a ∧ |inner ℝ (b - c) e₂| ≤ β) ∧
      (|inner ℝ (b + u - c - w) e₁| ≤ a ∧ |inner ℝ (b + u - c - w) e₂| ≤ β) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ t ht
    have hinterp (x y R : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
        |(1 - t) * x + t * y| ≤ R := by
      apply abs_le.mpr
      exact (convex_Icc (-R) R) (abs_le.mp hx) (abs_le.mp hy)
        (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have heq : b + t • u - c - t • w =
        (1 - t) • (b - c) + t • (b + u - c - w) := by module
    rw [heq, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
      inner_smul_left, inner_smul_left]
    exact ⟨hinterp _ _ _ h0.1 h1.1, hinterp _ _ _ h0.2 h1.2⟩

/-- Endpoint formulas give measurable fits for arbitrary measurable trace maps. -/
theorem measurableSet_fullTracePlank {α : Type*} [MeasurableSpace α]
    (b u : α → Plane) (hb : Measurable b) (hu : Measurable u)
    (c w e₁ e₂ : Plane) (a β : ℝ) :
    MeasurableSet {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} := by
  simp_rw [fullTracePlank_iff_endpoints]
  have h0 : Measurable (fun x => b x - c) := hb.sub_const _
  have h1 : Measurable (fun x => b x + u x - c - w) := ((hb.add hu).sub_const _).sub_const _
  exact ((measurableSet_le (h0.inner (𝕜 := ℝ)
      (measurable_const : Measurable (fun _ : α => e₁))).abs measurable_const).inter
      (measurableSet_le (h0.inner (𝕜 := ℝ)
        (measurable_const : Measurable (fun _ : α => e₂))).abs measurable_const)).inter
    ((measurableSet_le (h1.inner (𝕜 := ℝ)
      (measurable_const : Measurable (fun _ : α => e₁))).abs measurable_const).inter
      (measurableSet_le (h1.inner (𝕜 := ℝ)
        (measurable_const : Measurable (fun _ : α => e₂))).abs measurable_const))

/-- Candidate widths stay above the mesh scale and below a fixed chart scale. -/
structure PhysicalPlank (D : ℕ) where
  center : Plane
  speed : Plane
  axis₁ : Plane
  axis₂ : Plane
  narrow : ℝ
  wide : ℝ
  unit₁ : ‖axis₁‖ = 1
  unit₂ : ‖axis₂‖ = 1
  orthogonal : inner ℝ axis₁ axis₂ = 0
  narrow_ge_mesh : 1 / (D : ℝ) ≤ narrow
  narrow_le_wide : narrow ≤ wide
  wide_le_two : wide ≤ 2

def PhysicalPlank.fitSet {D : ℕ} {α : Type*} (p : PhysicalPlank D)
    (b u : α → Plane) : Set α :=
  {x | InFullTracePlank (b x) (u x) p.center p.speed p.axis₁ p.axis₂ p.narrow p.wide}

/-- Greedy geometric first-fit assignments retain half the original continuous
mass. Internal representative and mark-table complexities do not enter the chart
count or the assignments. -/
theorem continuous_plank_cover (H : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → Plane), Measurable b → Measurable u →
      (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ J : α → Finset (Fin D), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
    ∀ (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
    ∀ mass ρ : ℝ, 0 < mass → 0 < ρ → mass ≤ μ.real univ →
      (F.card : ℝ) ≤ mass * (D : ℝ) ^ 3 / ρ →
    ∃ m : ℕ, ∃ p : Fin m → PhysicalPlank D,
      (m : ℝ) ≤ (C * (D : ℝ) ^ (2 + ε) / ρ) * μ.real univ ∧
      (∀ j, (ρ / (C * (D : ℝ) ^ ε)) * (p j).narrow * (p j).wide ≤
        μ.real (firstAssignment (fun j => (p j).fitSet b u) j)) ∧
      mass / 2 ≤ ∑ j, μ.real (firstAssignment (fun j => (p j).fitSet b u) j) := by
  obtain ⟨η, hη, C, hC, hbound⟩ := scale_plank_mass_estimate H ε hε
  refine ⟨η, hη, 2 * C, by positivity, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong F hF mass ρ hmass hρ hm hcells
  classical
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  let A : ℝ := ρ / ((2 * C) * (D : ℝ) ^ ε)
  have hA : 0 < A := div_pos hρ (by positivity)
  let fit : PhysicalPlank D → Set α := fun p => p.fitSet b u
  have hfit (p : PhysicalPlank D) : MeasurableSet (fit p) :=
    measurableSet_fullTracePlank b u hb hu _ _ _ _ _ _
  let threshold : PhysicalPlank D → ℝ := fun p => A * p.narrow * p.wide
  have hfloor (p : PhysicalPlank D) : A / (D : ℝ) ^ 2 ≤ threshold p := by
    have hn : 0 ≤ p.narrow := (by positivity : (0 : ℝ) ≤ 1 / D).trans p.narrow_ge_mesh
    have hw : 1 / (D : ℝ) ≤ p.wide := p.narrow_ge_mesh.trans p.narrow_le_wide
    have hprod := mul_le_mul p.narrow_ge_mesh hw (by positivity : (0 : ℝ) ≤ 1 / D) hn
    calc
      _ = A * ((1 / (D : ℝ)) * (1 / D)) := by field_simp
      _ ≤ A * (p.narrow * p.wide) := mul_le_mul_of_nonneg_left hprod hA.le
      _ = _ := by ring
  obtain ⟨l, hg, hstop⟩ := exists_threshold_greedy_exhaustion fit hfit threshold μ
    (show 0 < A / (D : ℝ) ^ 2 by positivity) hfloor
  let p : Fin l.length → PhysicalPlank D := l.get
  let S : Fin l.length → Set α := firstAssignment (fun j => fit (p j))
  have hS (j : Fin l.length) : MeasurableSet (S j) :=
    measurableSet_firstAssignment _ (fun j => hfit (p j)) j
  have hdisj : Pairwise (fun i j => Disjoint (S i) (S j)) := firstAssignment_disjoint _
  have hpacket (j : Fin l.length) : threshold (p j) ≤ μ.real (S j) := by
    have h := hg.mass_at j
    rw [residualMeasure_eq fit hfit, measureReal_restrict_apply (hfit _)] at h
    have heq : fit (l.get j) ∩ (⋃ b ∈ l.take j.val, fit b)ᶜ =
        fit (l.get j) \ ⋃ b ∈ l.take j.val, fit b := by ext x; rfl
    rw [heq] at h
    simpa only [S, p, firstAssignment_get] using h
  have hU : (⋃ j, S j) = ⋃ p ∈ l, fit p := by
    calc
      _ = ⋃ j : Fin l.length, fit (p j) := iUnion_firstAssignment _
      _ = ⋃ q ∈ l, fit q := by
        ext x
        simp only [Set.mem_iUnion, exists_prop, p]
        exact (List.exists_mem_iff_get (l := l) (p := fun q => x ∈ fit q)).symm
  let R := (⋃ j, S j)ᶜ
  have hR : MeasurableSet R := (MeasurableSet.iUnion hS).compl
  have hres : residualMeasure fit μ l = μ.restrict R := by
    rw [residualMeasure_eq fit hfit, ← hU]
  have hcap : ScalePlankCap D (μ.restrict R) b u A := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ
    let q : PhysicalPlank D := ⟨c, w, e₁, e₂, a, β, he₁, he₂, he, ha, hab, hβ⟩
    have hs := (hstop q).le
    rw [hres] at hs
    calc
      _ = ENNReal.ofReal ((μ.restrict R).real (fit q)) :=
        (ENNReal.ofReal_toReal (measure_ne_top (μ.restrict R) _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hs
  have hμ := hbound D hD α (μ.restrict R) b u hb hu hbu J hJ hlong A hA hcap F hF
  rw [measureReal_restrict_apply_univ] at hμ
  have hscale : C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 3 *
      (mass * (D : ℝ) ^ 3 / ρ) = mass / 2 := by dsimp [A]; field_simp
  have hresmass : μ.real R ≤ mass / 2 := by
    apply hμ.trans
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hcells (by positivity)
  have hcovered : mass / 2 ≤ μ.real (⋃ j, S j) := by
    have hc := measureReal_compl (μ := μ) (MeasurableSet.iUnion hS)
    change μ.real R = _ at hc
    linarith
  have hsum : ∑ j, μ.real (S j) ≤ μ.real univ := by
    rw [← measureReal_iUnion_fintype hdisj hS]
    exact measureReal_mono (subset_univ _)
  have hbudget : (l.length : ℝ) * (A / (D : ℝ) ^ 2) ≤ μ.real univ := by
    calc
      _ = ∑ _j : Fin l.length, A / (D : ℝ) ^ 2 := by simp
      _ ≤ ∑ j, μ.real (S j) := Finset.sum_le_sum (fun j _ => (hfloor (p j)).trans (hpacket j))
      _ ≤ _ := hsum
  have hcount : (l.length : ℝ) ≤ ((2 * C) * (D : ℝ) ^ (2 + ε) / ρ) * μ.real univ := by
    calc
      _ ≤ μ.real univ / (A / (D : ℝ) ^ 2) := (le_div_iff₀ (by positivity)).mpr hbudget
      _ = _ := by
        rw [Real.rpow_add hd, Real.rpow_two]
        dsimp [A]
        field_simp <;> ring
  refine ⟨l.length, p, hcount, hpacket, ?_⟩
  rw [measureReal_iUnion_fintype (μ := μ) hdisj hS] at hcovered
  exact hcovered

end Submission.Lib.K4FinitePlankAtlases
