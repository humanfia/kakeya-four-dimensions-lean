import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Coarsen
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Projection

/-!
# Quantities determined by the scalar bin

`Determined E S D t q Φ δ n`: on the trajectories of `D` labelled at time `t`, the real quantity
`Φ` lies within `δ` of one of at most `n` centres prescribed by the `q`-bin of `S l`.  This is the
deterministic form of the paper's "negligible entropy given `T, S_l(t)_q`".  The calculus below:
sums, scalar multiples, perturbations, monotonicity, change of the conditioning bin, and the
projection estimate (`Determined` tangential coordinate ⇒ small mass).
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set

noncomputable section

variable {Λ : Type*}

/-- `Φ` is determined within `δ`, up to `n` candidates, by the `q`-bin of `S`. -/
def Determined (E : Set (Λ × ℝ)) (S : Λ → ℝ) (D : Set Λ) (t q : ℝ) (Φ : Λ → ℝ) (δ : ℝ)
    (n : ℕ) : Prop :=
  ∃ Y : ℤ → Finset ℝ, (∀ σ, (Y σ).card ≤ n) ∧
    ∀ l ∈ D, (l, t) ∈ E → ∃ y ∈ Y ⌊S l / q⌋, |Φ l - y| ≤ δ

namespace Determined

variable {E : Set (Λ × ℝ)} {S : Λ → ℝ} {D D' : Set Λ} {t q δ δ' : ℝ} {n n' : ℕ}
  {Φ Ψ : Λ → ℝ}

theorem mono_set (h : Determined E S D t q Φ δ n) (hD : D' ⊆ D) :
    Determined E S D' t q Φ δ n := by
  obtain ⟨Y, hY, hmem⟩ := h
  exact ⟨Y, hY, fun l hl => hmem l (hD hl)⟩

theorem mono (h : Determined E S D t q Φ δ n) (hδ : δ ≤ δ') (hn : n ≤ n') :
    Determined E S D t q Φ δ' n' := by
  obtain ⟨Y, hY, hmem⟩ := h
  refine ⟨Y, fun σ => (hY σ).trans hn, fun l hl hlt => ?_⟩
  obtain ⟨y, hy, hd⟩ := hmem l hl hlt
  exact ⟨y, hy, hd.trans hδ⟩

/-- Perturbation by a uniformly small quantity. -/
theorem perturb (h : Determined E S D t q Φ δ n) {ε : ℝ}
    (hε : ∀ l ∈ D, (l, t) ∈ E → |Ψ l - Φ l| ≤ ε) : Determined E S D t q Ψ (δ + ε) n := by
  obtain ⟨Y, hY, hmem⟩ := h
  refine ⟨Y, hY, fun l hl hlt => ?_⟩
  obtain ⟨y, hy, hd⟩ := hmem l hl hlt
  refine ⟨y, hy, ?_⟩
  calc |Ψ l - y| ≤ |Ψ l - Φ l| + |Φ l - y| := abs_sub_le _ _ _
    _ ≤ ε + δ := add_le_add (hε l hl hlt) hd
    _ = δ + ε := add_comm _ _

/-- Pointwise equality on the labelled trajectories of `D`. -/
theorem congr (h : Determined E S D t q Φ δ n) (hΦΨ : ∀ l ∈ D, (l, t) ∈ E → Φ l = Ψ l) :
    Determined E S D t q Ψ δ n := by
  obtain ⟨Y, hY, hmem⟩ := h
  refine ⟨Y, hY, fun l hl hlt => ?_⟩
  obtain ⟨y, hy, hd⟩ := hmem l hl hlt
  exact ⟨y, hy, by rwa [← hΦΨ l hl hlt]⟩

/-- Sums. -/
theorem add (h : Determined E S D t q Φ δ n) (h' : Determined E S D t q Ψ δ' n') :
    Determined E S D t q (fun l => Φ l + Ψ l) (δ + δ') (n * n') := by
  classical
  obtain ⟨Y, hY, hmem⟩ := h
  obtain ⟨Y', hY', hmem'⟩ := h'
  refine ⟨fun σ => ((Y σ) ×ˢ (Y' σ)).image (fun p => p.1 + p.2), fun σ => ?_, fun l hl hlt => ?_⟩
  · calc _ ≤ ((Y σ) ×ˢ (Y' σ)).card := Finset.card_image_le
      _ = (Y σ).card * (Y' σ).card := Finset.card_product _ _
      _ ≤ n * n' := Nat.mul_le_mul (hY σ) (hY' σ)
  · obtain ⟨y, hy, hd⟩ := hmem l hl hlt
    obtain ⟨y', hy', hd'⟩ := hmem' l hl hlt
    refine ⟨y + y', Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.mpr ⟨hy, hy'⟩, rfl⟩, ?_⟩
    calc |Φ l + Ψ l - (y + y')| = |(Φ l - y) + (Ψ l - y')| := by ring_nf
      _ ≤ |Φ l - y| + |Ψ l - y'| := abs_add_le _ _
      _ ≤ δ + δ' := add_le_add hd hd'

/-- Scalar multiples by a constant. -/
theorem const_mul (h : Determined E S D t q Φ δ n) (a : ℝ) :
    Determined E S D t q (fun l => a * Φ l) (|a| * δ) n := by
  classical
  obtain ⟨Y, hY, hmem⟩ := h
  refine ⟨fun σ => (Y σ).image (fun y => a * y), fun σ => Finset.card_image_le.trans (hY σ),
    fun l hl hlt => ?_⟩
  obtain ⟨y, hy, hd⟩ := hmem l hl hlt
  refine ⟨a * y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg a)

theorem neg (h : Determined E S D t q Φ δ n) :
    Determined E S D t q (fun l => -Φ l) δ n := by
  have := h.const_mul (-1)
  simpa using this

theorem sub (h : Determined E S D t q Φ δ n) (h' : Determined E S D t q Ψ δ' n') :
    Determined E S D t q (fun l => Φ l - Ψ l) (δ + δ') (n * n') := by
  have := h.add h'.neg
  simpa [sub_eq_add_neg] using this

/-- A quantity known exactly up to a function of the bin. -/
theorem of_bin (f : ℤ → ℝ) (hf : ∀ l ∈ D, (l, t) ∈ E → Φ l = f ⌊S l / q⌋) :
    Determined E S D t q Φ 0 1 := by
  refine ⟨fun σ => {f σ}, fun σ => by simp, fun l hl hlt => ⟨f ⌊S l / q⌋, by simp, ?_⟩⟩
  rw [hf l hl hlt]; simp

/-- The scalar itself is determined by its bin within `q`. -/
theorem self (hq : 0 < q) : Determined E S D t q S q 1 := by
  refine ⟨fun σ => {σ * q}, fun σ => by simp, fun l _ _ => ⟨⌊S l / q⌋ * q, by simp, ?_⟩⟩
  have h1 := Int.floor_le (S l / q)
  have h2 := Int.lt_floor_add_one (S l / q)
  have h1' : (⌊S l / q⌋ : ℝ) * q ≤ S l := by
    have := mul_le_mul_of_nonneg_right h1 hq.le; rwa [div_mul_cancel₀ _ hq.ne'] at this
  have h2' : S l < (⌊S l / q⌋ : ℝ) * q + q := by
    have := mul_lt_mul_of_pos_right h2 hq; rw [div_mul_cancel₀ _ hq.ne'] at this; linarith
  rw [abs_le]; constructor <;> linarith

/-- Constants are determined. -/
theorem const (a : ℝ) : Determined E S D t q (fun _ => a) 0 1 :=
  of_bin (fun _ => a) (fun _ _ _ => rfl)

/-- Change of the conditioning variable: if `Φ` is determined by the `q`-bin of `S'` (on the
trajectories labelled at time `t'`) and `S'` is determined by the `q`-bin of `S` within `δS`
(with `n_S` candidates), then `Φ` is determined by the `q`-bin of `S`. -/
theorem transport {S' : Λ → ℝ} {t' δS : ℝ} {nS : ℕ} (hq : 0 < q)
    (hΦ : Determined E S' D t' q Φ δ n) (hS : Determined E S D t q S' δS nS)
    (hlab : ∀ l ∈ D, (l, t) ∈ E → (l, t') ∈ E) (hδS : 0 ≤ δS) :
    Determined E S D t q Φ δ (n * (nS * (⌊2 * δS / q⌋₊ + 2))) := by
  classical
  obtain ⟨Y, hY, hmem⟩ := hΦ
  obtain ⟨Z, hZ, hZmem⟩ := hS
  -- the bins of `S'` compatible with a centre `z`
  let bins : ℝ → Finset ℤ := fun z => Finset.Icc ⌊(z - δS) / q⌋ ⌊(z + δS) / q⌋
  have hbins : ∀ z, (bins z).card ≤ ⌊2 * δS / q⌋₊ + 2 := by
    intro z
    have := card_Icc_floor_le (y₀ := z) hq hδS
    have h2 : (2 * δS / q + 2 : ℝ) < (⌊2 * δS / q⌋₊ + 2 : ℕ) + 1 := by
      push_cast; linarith [Nat.lt_floor_add_one (2 * δS / q)]
    have : ((bins z).card : ℝ) < ((⌊2 * δS / q⌋₊ + 2 : ℕ) : ℝ) + 1 := lt_of_le_of_lt this h2
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  refine ⟨fun σ => ((Z σ).biUnion bins).biUnion Y, fun σ => ?_, fun l hl hlt => ?_⟩
  · calc _ ≤ ∑ σ' ∈ (Z σ).biUnion bins, (Y σ').card := Finset.card_biUnion_le
      _ ≤ ∑ _σ' ∈ (Z σ).biUnion bins, n := Finset.sum_le_sum fun σ' _ => hY σ'
      _ = ((Z σ).biUnion bins).card * n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (∑ z ∈ Z σ, (bins z).card) * n := Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ ≤ (∑ _z ∈ Z σ, (⌊2 * δS / q⌋₊ + 2)) * n :=
          Nat.mul_le_mul_right _ (Finset.sum_le_sum fun z _ => hbins z)
      _ = (Z σ).card * (⌊2 * δS / q⌋₊ + 2) * n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ nS * (⌊2 * δS / q⌋₊ + 2) * n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hZ σ))
      _ = n * (nS * (⌊2 * δS / q⌋₊ + 2)) := by ring
  · obtain ⟨z, hz, hdz⟩ := hZmem l hl hlt
    obtain ⟨y, hy, hdy⟩ := hmem l hl (hlab l hl hlt)
    refine ⟨y, Finset.mem_biUnion.mpr ⟨⌊S' l / q⌋, Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩, hy⟩, hdy⟩
    exact floor_mem_Icc_of_abs_le hq hdz

/-- Finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) (Φs : ι → Λ → ℝ) (δs : ι → ℝ) (ns : ι → ℕ)
    (h : ∀ i ∈ s, Determined E S D t q (Φs i) (δs i) (ns i)) :
    Determined E S D t q (fun l => ∑ i ∈ s, Φs i l) (∑ i ∈ s, δs i) (∏ i ∈ s, ns i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (const (E := E) (S := S) (D := D) (t := t) (q := q) (0 : ℝ))
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact this

end Determined

/-- **Projection estimate, `Determined` form.**  If the tangential coordinate at time `t` is
determined within `L` by the `q`-bin of the scalar (up to `n` candidates) on the labelled
trajectories of `D`, these carry prior mass at most `400 K⁵ n (L + q)`. -/
theorem Determined.mass_le {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 5 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d) (hd1 : d ≤ 1) {D : Set Λ} {t q L : ℝ} {n : ℕ}
    (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hL : 0 ≤ L)
    (h : Determined E (fun l => zS F (c l) t) D t q (fun l => zy (c l) t) L n) :
    ν {l | l ∈ D ∧ (l, t) ∈ E} ≤ ENNReal.ofReal (400 * K ^ 5 * n * (L + q)) := by
  obtain ⟨Y, hY, hmem⟩ := h
  refine (measure_mono ?_).trans (thin_y_mass hSN hd1 t q L hζq hq1 hL Y n hY)
  rintro l ⟨hl, hlt⟩
  obtain ⟨y, hy, hd⟩ := hmem l hl hlt
  exact ⟨hlt, y, hy, hd⟩

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
