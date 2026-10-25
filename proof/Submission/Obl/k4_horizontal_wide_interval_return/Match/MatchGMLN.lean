/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchGMLN.lean (namespace renamed into o250's). -/
import Mathlib
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchQuad
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchCor
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchJitter
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchGroup
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchGroupN

/-!
# The sliced general matching lemma

Members carry full coefficient vectors `F : Fin n → ℝ`; finitely many linear slices
`S j : (Fin n → ℝ) → (Fin 3 → ℝ)` give one-variable quadratics, every coordinate of `F`
is recovered from some slice (`hrec`), and the pair law makes the two members close
in every slice. Jet counts are for the full vectors. Then pairs whose full vectors
differ by at least `M*` in some coordinate carry at most `A (M*/δ)^(-η)` of the
reference weight.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.MatchGMLN

open MeasureTheory MatchQuad MatchCor MatchJitter MatchGroup MatchGroupN

/-- The admissible bin offsets in dimension `n`. -/
def offsN (n : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => Finset.Icc (-2 : ℤ) 2)

lemma card_offsN (n : ℕ) : (offsN n).card = 5 ^ n := by
  unfold offsN; rw [Fintype.card_piFinset]; simp

lemma binN_diff_mem {n : ℕ} {M : ℝ} (hM : 0 < M) (F F' : Fin n → ℝ)
    (h : ∀ k, |F k - F' k| < 2 * M) : binN M F' - binN M F ∈ offsN n := by
  unfold offsN
  rw [Fintype.mem_piFinset]
  intro k
  have hk := h k
  rw [abs_lt] at hk
  have e1 := Int.floor_le (F k / M)
  have e2 := Int.lt_floor_add_one (F k / M)
  have e3 := Int.floor_le (F' k / M)
  have e4 := Int.lt_floor_add_one (F' k / M)
  have d1 : F' k / M - F k / M < 2 := by
    rw [← sub_div, div_lt_iff₀ hM]; linarith
  have d2 : -2 < F' k / M - F k / M := by
    rw [← sub_div, lt_div_iff₀ hM]; linarith
  simp only [Pi.sub_apply, binN, Finset.mem_Icc]
  constructor
  · have : ((⌊F' k / M⌋ - ⌊F k / M⌋ : ℤ) : ℝ) > -3 := by push_cast; linarith
    have : (⌊F' k / M⌋ - ⌊F k / M⌋ : ℤ) > -3 := by exact_mod_cast this
    omega
  · have : ((⌊F' k / M⌋ - ⌊F k / M⌋ : ℤ) : ℝ) < 3 := by push_cast; linarith
    have : (⌊F' k / M⌋ - ⌊F k / M⌋ : ℤ) < 3 := by exact_mod_cast this
    omega

section Scale

variable {n m : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
  [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]

/-- Pairs at dyadic scale `M` in the full coefficients. -/
def bandN (M : ℝ) (F₁ : ι₁ → Fin n → ℝ) (F₂ : ι₂ → Fin n → ℝ) : Set ((ι₁ × ι₂) × ℝ) :=
  {p | (∃ k, M ≤ |F₁ p.1.1 k - F₂ p.1.2 k|) ∧ ∀ k, |F₁ p.1.1 k - F₂ p.1.2 k| < 2 * M}

theorem scaleN_le {d η L N₀ : ℝ} (hQ : MatchQL d η L N₀) (hη : 0 < η)
    (S : Fin m → (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) {Lop Crec : ℝ} (hLop : 0 ≤ Lop) (hCrec : 0 < Crec)
    (hop : ∀ j (F : Fin n → ℝ) (X : ℝ), (∀ k, |F k| ≤ X) → ∀ k, |S j F k| ≤ Lop * X)
    (hrec : ∀ (F : Fin n → ℝ) (X : ℝ), (∃ k, X ≤ |F k|) → ∃ j, X / Crec ≤ cnorm (S j F))
    (hL : 3 * Lop * Crec ≤ L)
    (F₁ : ι₁ → Fin n → ℝ) (F₂ : ι₂ → Fin n → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
    (Q : Measure ((ι₁ × ι₂) × ℝ)) [IsFiniteMeasure Q]
    {δ M A : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hN : N₀ ≤ M / (Crec * δ)) (hA1 : 1 ≤ A)
    (hA : A ≤ (M / (Crec * δ)) ^ η) (hAc : A * (M / δ) ^ d ≤ (M / (Crec * δ)) ^ (d + η))
    (hT₁ : ∀ i, 0 ≤ T₁ i) (hT₂ : ∀ j, 0 ≤ T₂ j)
    (hm₁ : ∀ i (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E)
    (hm₂ : ∀ j (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E)
    (hc₁ : ∀ r : Fin n → ℝ,
      ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hc₂ : ∀ r : Fin n → ℝ,
      ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hae : ∀ᵐ p ∂Q, p.2 ∈ Set.Icc (0:ℝ) 1 ∧ ∀ j,
      |quad (S j (F₁ p.1.1)) p.2 - quad (S j (F₂ p.1.2)) p.2| ≤ 2 * δ) :
    Q (bandN M F₁ F₂) ≤
      ENNReal.ofReal (m * 5 ^ n * (A * (M / (Crec * δ)) ^ (-η)) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  classical
  set θ := A * (M / (Crec * δ)) ^ (-η) with hθ
  have hθnn : 0 ≤ θ :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt (div_pos hM (mul_pos hCrec hδ))) _)
  set img := Finset.univ.image (fun i => binN M (F₁ i)) with himg
  let W₁ : (Fin n → ℤ) → ℝ := fun β => ∑ i ∈ Finset.univ.filter (fun i => binN M (F₁ i) = β), T₁ i
  let W₂ : (Fin n → ℤ) → ℝ := fun γ => ∑ j ∈ Finset.univ.filter (fun j => binN M (F₂ j) = γ), T₂ j
  have hW₁nn : ∀ β, 0 ≤ W₁ β := fun β => Finset.sum_nonneg (fun i _ => hT₁ i)
  have hW₂nn : ∀ γ, 0 ≤ W₂ γ := fun γ => Finset.sum_nonneg (fun j _ => hT₂ j)
  have hcover : bandN M F₁ F₂ ⊆
      ⋃ j ∈ (Finset.univ : Finset (Fin m)), ⋃ β ∈ img, ⋃ δb ∈ offsN n,
        groupN M Crec (S j) F₁ F₂ β δb := by
    intro p hp
    obtain ⟨⟨k, hk⟩, h2⟩ := hp
    obtain ⟨j, hj⟩ := hrec (F₁ p.1.1 - F₂ p.1.2) M ⟨k, by simpa using hk⟩
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨j, Finset.mem_univ _, binN M (F₁ p.1.1), by simp [himg],
      binN M (F₂ p.1.2) - binN M (F₁ p.1.1), binN_diff_mem hM _ _ h2, ?_⟩
    refine ⟨rfl, by simp, ?_⟩
    rw [← map_sub]; exact hj
  have hgroup : ∀ j β δb, δb ∈ offsN n →
      Q (groupN M Crec (S j) F₁ F₂ β δb) ≤ ENNReal.ofReal (θ * (W₁ β + W₂ (β + δb))) := by
    intro j β δb hδb
    have hδb' : ∀ k, |δb k| ≤ 2 := by
      intro k
      have := (Fintype.mem_piFinset.mp hδb) k
      rw [Finset.mem_Icc] at this
      rw [abs_le]; exact this
    exact groupN_le hQ hη (S j) hLop hCrec (hop j) hL F₁ F₂ T₁ T₂ Q hδ hM hN hA1 hA hAc hT₁ hT₂
      hm₁ hm₂ hc₁ hc₂ (by filter_upwards [hae] with p hp; exact ⟨hp.1, hp.2 j⟩) β δb hδb'
  have hsumW₁ : ∑ β ∈ img, W₁ β = ∑ i, T₁ i := by
    rw [himg]
    exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) T₁
  have hsumW₂ : ∀ δb, ∑ β ∈ img, W₂ (β + δb) ≤ ∑ j, T₂ j := by
    intro δb
    have himgW : ∑ β ∈ img, W₂ (β + δb) = ∑ γ ∈ img.image (fun β => β + δb), W₂ γ :=
      (Finset.sum_image (s := img) (g := fun β : Fin n → ℤ => β + δb) (f := W₂)
        (fun x _ y _ hxy => by simpa using hxy)).symm
    rw [himgW]
    set img₂ := Finset.univ.image (fun j => binN M (F₂ j))
    calc ∑ γ ∈ img.image (fun β => β + δb), W₂ γ
        ≤ ∑ γ ∈ img.image (fun β => β + δb) ∪ img₂, W₂ γ :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun γ _ _ => hW₂nn γ)
      _ = ∑ γ ∈ img₂, W₂ γ := by
          refine (Finset.sum_subset Finset.subset_union_right ?_).symm
          intro γ _ hγ
          apply Finset.sum_eq_zero
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exfalso; apply hγ; rw [← hj]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
      _ = ∑ j, T₂ j :=
          Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem _ hj) T₂
  have hinner : ∀ j : Fin m, ∑ β ∈ img, ∑ δb ∈ offsN n, θ * (W₁ β + W₂ (β + δb)) ≤
      5 ^ n * θ * (∑ i, T₁ i + ∑ j, T₂ j) := by
    intro j
    have e1 : ∑ β ∈ img, ∑ δb ∈ offsN n, θ * (W₁ β + W₂ (β + δb)) =
        θ * (∑ β ∈ img, ∑ δb ∈ offsN n, W₁ β + ∑ β ∈ img, ∑ δb ∈ offsN n, W₂ (β + δb)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∑ β ∈ img, ∑ δb ∈ offsN n, W₁ β = 5 ^ n * ∑ i, T₁ i := by
      simp only [Finset.sum_const, card_offsN, nsmul_eq_mul]
      rw [← Finset.mul_sum, hsumW₁]; norm_num
    have e3 : ∑ β ∈ img, ∑ δb ∈ offsN n, W₂ (β + δb) ≤ 5 ^ n * ∑ j, T₂ j := by
      rw [Finset.sum_comm]
      calc ∑ δb ∈ offsN n, ∑ β ∈ img, W₂ (β + δb) ≤ ∑ δb ∈ offsN n, ∑ j, T₂ j :=
            Finset.sum_le_sum (fun δb _ => hsumW₂ δb)
        _ = 5 ^ n * ∑ j, T₂ j := by
            simp only [Finset.sum_const, card_offsN, nsmul_eq_mul]; norm_num
    rw [e1, e2]
    have : θ * (5 ^ n * ∑ i, T₁ i + ∑ β ∈ img, ∑ δb ∈ offsN n, W₂ (β + δb)) ≤
        θ * (5 ^ n * ∑ i, T₁ i + 5 ^ n * ∑ j, T₂ j) := by gcongr
    linarith
  calc Q (bandN M F₁ F₂)
      ≤ Q (⋃ j ∈ (Finset.univ : Finset (Fin m)), ⋃ β ∈ img, ⋃ δb ∈ offsN n,
          groupN M Crec (S j) F₁ F₂ β δb) := measure_mono hcover
    _ ≤ ∑ j : Fin m, ∑ β ∈ img, ∑ δb ∈ offsN n, Q (groupN M Crec (S j) F₁ F₂ β δb) := by
        refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
        refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum (fun β _ => ?_))
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ j : Fin m, ∑ β ∈ img, ∑ δb ∈ offsN n, ENNReal.ofReal (θ * (W₁ β + W₂ (β + δb))) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun β _ =>
          Finset.sum_le_sum (fun δb hδb => hgroup j β δb hδb)))
    _ = ENNReal.ofReal (∑ j : Fin m, ∑ β ∈ img, ∑ δb ∈ offsN n, θ * (W₁ β + W₂ (β + δb))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [ENNReal.ofReal_sum_of_nonneg]
          · refine Finset.sum_congr rfl (fun β _ => ?_)
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro δb _; exact mul_nonneg hθnn (add_nonneg (hW₁nn _) (hW₂nn _))
          · intro β _
            exact Finset.sum_nonneg (fun δb _ => mul_nonneg hθnn (add_nonneg (hW₁nn _) (hW₂nn _)))
        · intro j _
          exact Finset.sum_nonneg (fun β _ => Finset.sum_nonneg
            (fun δb _ => mul_nonneg hθnn (add_nonneg (hW₁nn _) (hW₂nn _))))
    _ ≤ ENNReal.ofReal (m * 5 ^ n * θ * (∑ i, T₁ i + ∑ j, T₂ j)) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∑ j : Fin m, ∑ β ∈ img, ∑ δb ∈ offsN n, θ * (W₁ β + W₂ (β + δb))
            ≤ ∑ j : Fin m, 5 ^ n * θ * (∑ i, T₁ i + ∑ j, T₂ j) :=
              Finset.sum_le_sum (fun j _ => hinner j)
          _ = m * 5 ^ n * θ * (∑ i, T₁ i + ∑ j, T₂ j) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Scale

/-- **The sliced general matching lemma.** -/
theorem gmlN (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) {n m : ℕ}
    (S : Fin m → (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) {Lop Crec : ℝ} (hLop : 0 ≤ Lop) (hCrec : 1 ≤ Crec)
    (hop : ∀ j (F : Fin n → ℝ) (X : ℝ), (∀ k, |F k| ≤ X) → ∀ k, |S j F k| ≤ Lop * X)
    (hrec : ∀ (F : Fin n → ℝ) (X : ℝ), (∃ k, X ≤ |F k|) → ∃ j, X / Crec ≤ cnorm (S j F)) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (F₁ : ι₁ → Fin n → ℝ) (F₂ : ι₂ → Fin n → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
      (P : Measure ((ι₁ × ι₂) × ℝ)) [IsFiniteMeasure P] (δ Mst A B w : ℝ),
      0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
      0 < w → w ≤ 1 / 4 → 6 * B * w ≤ δ →
      (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
      (∀ j' i k, |S j' (F₁ i) k| ≤ B) → (∀ j' i k, |S j' (F₂ i) k| ≤ B) →
      (∀ i (x : ℝ), P {p | p.1.1 = i ∧ p.2 ∈ Set.Icc (x - w) x} ≤ ENNReal.ofReal (A * T₁ i * w)) →
      (∀ j (x : ℝ), P {p | p.1.2 = j ∧ p.2 ∈ Set.Icc (x - w) x} ≤ ENNReal.ofReal (A * T₂ j * w)) →
      (∀ (r : Fin n → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ (r : Fin n → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ᵐ p ∂P, p.2 ∈ Set.Icc (1/4 : ℝ) (3/4) ∧ ∀ j',
        |quad (S j' (F₁ p.1.1)) p.2 - quad (S j' (F₂ p.1.2)) p.2| ≤ δ) →
      P {p | ∃ k, Mst ≤ |F₁ p.1.1 k - F₂ p.1.2 k|} ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  obtain ⟨η₀, hη₀, HL⟩ := matchQL_of_hyp hM hd0 hd1
  have hCpos : 0 < Crec := by linarith
  set L : ℝ := 3 * Lop * Crec + 1 with hLdef
  have hL1 : 1 ≤ L := by have : 0 ≤ 3 * Lop * Crec := by positivity
                         linarith
  obtain ⟨N₀, hN₀, hQ⟩ := HL L hL1
  set ρ : ℝ := (2:ℝ) ^ (-η₀) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set G : ℝ := Crec ^ (d + η₀) * ((m:ℝ) + 1) * 5 ^ n / (1 - ρ) with hG
  have hCdη : 1 ≤ Crec ^ (d + η₀) := Real.one_le_rpow hCrec (by linarith)
  have hCη : Crec ^ η₀ ≤ Crec ^ (d + η₀) := Real.rpow_le_rpow_of_exponent_le hCrec (by linarith)
  have hG1 : Crec ^ (d + η₀) ≤ G := by
    rw [hG, le_div_iff₀ (by linarith)]
    have h5 : (1:ℝ) ≤ 5 ^ n := one_le_pow₀ (by norm_num)
    have hm1 : (1:ℝ) ≤ (m:ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
    have h1ρ : 1 - ρ ≤ 1 := by linarith
    have : Crec ^ (d + η₀) * 1 * 1 ≤ Crec ^ (d + η₀) * ((m:ℝ) + 1) * 5 ^ n := by gcongr
    nlinarith [hCdη]
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one (le_trans hCdη hG1)
  refine ⟨η₀ / 4, by positivity, max (max (Crec * N₀) 1) (G ^ (4 / (3 * η₀))),
    le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  intro ι₁ ι₂ _ _ _ _ _ _ F₁ F₂ T₁ T₂ P _ δ Mst A B w hδ hMst hA1 hA hw hw4 hwδ hT₁ hT₂
    hB₁ hB₂ hi₁ hi₂ hc₁ hc₂ hae
  classical
  have hR : max (max (Crec * N₀) 1) (G ^ (4 / (3 * η₀))) ≤ Mst / δ := by
    rw [le_div_iff₀ hδ]; exact hMst
  have hCN₀ : Crec * N₀ ≤ Mst / δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have h1M : 1 ≤ Mst / δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hGM : G ^ (4 / (3 * η₀)) ≤ Mst / δ := le_trans (le_max_right _ _) hR
  have hX0 : 0 < Mst / δ := lt_of_lt_of_le zero_lt_one h1M
  have hMstpos : 0 < Mst := by
    have := mul_le_mul_of_nonneg_right h1M (le_of_lt hδ)
    rw [div_mul_cancel₀ _ (ne_of_gt hδ), one_mul] at this; linarith
  -- `G ≤ X^(3η₀/4)` for `X = Mst/δ`
  have hGX : G ≤ (Mst / δ) ^ (3 * η₀ / 4) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hGpos) _) hGM
      (by positivity : (0:ℝ) ≤ 3 * η₀ / 4)
    rwa [← Real.rpow_mul (le_of_lt hGpos), show 4 / (3 * η₀) * (3 * η₀ / 4) = 1 by
      field_simp, Real.rpow_one] at this
  -- the jittered law
  set Q := jitter P w with hQdef
  have hQidx : ∀ S : Set (ι₁ × ι₂), Q {p | p.1 ∈ S} = P {p | p.1 ∈ S} :=
    fun S => jitter_index P hw (measurableSet_index S)
  haveI : IsFiniteMeasure Q := ⟨by
    have := hQidx Set.univ
    simp only [Set.mem_univ, Set.setOf_true] at this
    rw [this]; exact measure_lt_top P _⟩
  have hm₁ : ∀ i (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E := by
    intro i E hE
    have := jitter_marginal P hw (S := {x : ι₁ × ι₂ | x.1 = i}) (measurableSet_index _)
      (C := ENNReal.ofReal (A * T₁ i)) (by
        intro x
        rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) (hT₁ i))]
        exact hi₁ i x) hE
    simpa using this
  have hm₂ : ∀ j (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E := by
    intro j E hE
    have := jitter_marginal P hw (S := {x : ι₁ × ι₂ | x.2 = j}) (measurableSet_index _)
      (C := ENNReal.ofReal (A * T₂ j)) (by
        intro x
        rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) (hT₂ j))]
        exact hi₂ j x) hE
    simpa using this
  have hQae : ∀ᵐ p ∂Q, p.2 ∈ Set.Icc (0:ℝ) 1 ∧ ∀ j',
      |quad (S j' (F₁ p.1.1)) p.2 - quad (S j' (F₂ p.1.2)) p.2| ≤ 2 * δ := by
    refine ae_jitter P (R := fun x y => y ∈ Set.Icc (1/4 : ℝ) (3/4) ∧ ∀ j',
        |quad (S j' (F₁ x.1)) y - quad (S j' (F₂ x.2)) y| ≤ δ)
      (R' := fun x y => y ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j',
        |quad (S j' (F₁ x.1)) y - quad (S j' (F₂ x.2)) y| ≤ 2 * δ) ?_ hae ?_
    · have hf : ∀ j', Measurable (fun p : (ι₁ × ι₂) × ℝ =>
          |quad (S j' (F₁ p.1.1)) p.2 - quad (S j' (F₂ p.1.2)) p.2|) := by
        intro j'
        apply measurable_from_prod_countable_right
        intro x
        simp only [quad]
        fun_prop
      have : {p : (ι₁ × ι₂) × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j',
          |quad (S j' (F₁ p.1.1)) p.2 - quad (S j' (F₂ p.1.2)) p.2| ≤ 2 * δ} =
          {p | p.2 ∈ Set.Icc (0 : ℝ) 1} ∩ ⋂ j', {p | |quad (S j' (F₁ p.1.1)) p.2 -
            quad (S j' (F₂ p.1.2)) p.2| ≤ 2 * δ} := by
        ext p; simp
      rw [this]
      exact (measurable_snd measurableSet_Icc).inter
        (MeasurableSet.iInter (fun j' => measurableSet_le (hf j') measurable_const))
    · intro x y z ⟨⟨hy1, hy2⟩, hval⟩ hz0 hzw
      refine ⟨⟨by linarith, by linarith⟩, fun j' => ?_⟩
      have hd : |quad (S j' (F₁ x.1)) (y + z) - quad (S j' (F₂ x.2)) (y + z)
          - (quad (S j' (F₁ x.1)) y - quad (S j' (F₂ x.2)) y)| ≤ 6 * B * z := by
        set a := S j' (F₁ x.1)
        set b := S j' (F₂ x.2)
        have e : quad a (y + z) - quad b (y + z) - (quad a y - quad b y)
            = (a 1 - b 1) * z + (a 2 - b 2) * (z * (2 * y + z)) := by
          simp [quad]; ring
        rw [e]
        have hb1 : |a 1 - b 1| ≤ 2 * B := by
          have := abs_sub (a 1) (b 1); linarith [hB₁ j' x.1 1, hB₂ j' x.2 1]
        have hb2 : |a 2 - b 2| ≤ 2 * B := by
          have := abs_sub (a 2) (b 2); linarith [hB₁ j' x.1 2, hB₂ j' x.2 2]
        have hyz : 0 ≤ z * (2 * y + z) := by positivity
        have hyz2 : z * (2 * y + z) ≤ 2 * z := by nlinarith
        have hB0 : 0 ≤ 2 * B := by linarith [abs_nonneg (a 0), hB₁ j' x.1 0]
        calc |(a 1 - b 1) * z + (a 2 - b 2) * (z * (2 * y + z))|
            ≤ |a 1 - b 1| * z + |a 2 - b 2| * (z * (2 * y + z)) := by
              refine le_trans (abs_add_le _ _) ?_
              rw [abs_mul, abs_mul, abs_of_nonneg hz0, abs_of_nonneg hyz]
          _ ≤ 2 * B * z + 2 * B * (2 * z) := by gcongr
          _ = 6 * B * z := by ring
      have hB0 : 0 ≤ B := by linarith [abs_nonneg (S j' (F₁ x.1) 0), hB₁ j' x.1 0]
      have : 6 * B * z ≤ δ := le_trans (by nlinarith) hwδ
      have := abs_sub_abs_le_abs_sub (quad (S j' (F₁ x.1)) (y + z) - quad (S j' (F₂ x.2)) (y + z))
        (quad (S j' (F₁ x.1)) y - quad (S j' (F₂ x.2)) y)
      linarith [hval j']
  -- each dyadic band
  have hband : ∀ k : ℕ, Q (bandN (Mst * 2 ^ k) F₁ F₂) ≤
      ENNReal.ofReal (m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) *
        (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) := by
    intro k
    have hMk : 0 < Mst * 2 ^ k := by positivity
    set X' := Mst * 2 ^ k / δ with hX'
    have hX'eq : X' = (Mst / δ) * 2 ^ k := by rw [hX']; ring
    have hge : Mst / δ ≤ X' := by
      rw [hX'eq]; exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
    have hX'pos : 0 < X' := lt_of_lt_of_le hX0 hge
    have hY : Mst * 2 ^ k / (Crec * δ) = X' / Crec := by rw [hX']; field_simp
    -- the three numerical conditions
    have hYge : (Mst / δ) / Crec ≤ X' / Crec := div_le_div_of_nonneg_right hge (le_of_lt hCpos)
    have hN' : N₀ ≤ Mst * 2 ^ k / (Crec * δ) := by
      rw [hY, le_div_iff₀ hCpos]
      calc N₀ * Crec = Crec * N₀ := by ring
        _ ≤ Mst / δ := hCN₀
        _ ≤ X' := hge
    have hXη : (Mst / δ) ^ (η₀ / 4) * Crec ^ (d + η₀) ≤ X' ^ η₀ := by
      calc (Mst / δ) ^ (η₀ / 4) * Crec ^ (d + η₀) ≤ (Mst / δ) ^ (η₀ / 4) * G := by gcongr
        _ ≤ (Mst / δ) ^ (η₀ / 4) * (Mst / δ) ^ (3 * η₀ / 4) := by gcongr
        _ = (Mst / δ) ^ η₀ := by rw [← Real.rpow_add hX0]; ring_nf
        _ ≤ X' ^ η₀ := Real.rpow_le_rpow (le_of_lt hX0) hge (le_of_lt hη₀)
    have hA' : A ≤ (Mst * 2 ^ k / (Crec * δ)) ^ η₀ := by
      rw [hY, Real.div_rpow (le_of_lt hX'pos) (le_of_lt hCpos), le_div_iff₀ (Real.rpow_pos_of_pos hCpos _)]
      calc A * Crec ^ η₀ ≤ (Mst / δ) ^ (η₀ / 4) * Crec ^ (d + η₀) := by gcongr
        _ ≤ X' ^ η₀ := hXη
    have hAc : A * (Mst * 2 ^ k / δ) ^ d ≤ (Mst * 2 ^ k / (Crec * δ)) ^ (d + η₀) := by
      rw [← hX', hY, Real.div_rpow (le_of_lt hX'pos) (le_of_lt hCpos),
        le_div_iff₀ (Real.rpow_pos_of_pos hCpos _), Real.rpow_add hX'pos]
      calc A * X' ^ d * Crec ^ (d + η₀) = X' ^ d * (A * Crec ^ (d + η₀)) := by ring
        _ ≤ X' ^ d * ((Mst / δ) ^ (η₀ / 4) * Crec ^ (d + η₀)) := by gcongr
        _ ≤ X' ^ d * X' ^ η₀ := by gcongr
    have := scaleN_le hQ hη₀ S hLop hCpos hop hrec (by linarith) F₁ F₂ T₁ T₂ Q hδ hMk hN' hA1
      hA' hAc hT₁ hT₂ hm₁ hm₂
      (fun r => hc₁ r _ (le_mul_of_one_le_right (le_of_lt hMstpos) (one_le_pow₀ (by norm_num))))
      (fun r => hc₂ r _ (le_mul_of_one_le_right (le_of_lt hMstpos) (one_le_pow₀ (by norm_num))))
      hQae
    refine le_trans this (le_of_eq ?_)
    congr 1
    rw [hY, Real.div_rpow (le_of_lt hX'pos) (le_of_lt hCpos), hX'eq,
      Real.mul_rpow (le_of_lt hX0) (by positivity)]
    have : ((2:ℝ) ^ k) ^ (-η₀) = ρ ^ k := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [this, Real.rpow_neg (le_of_lt hCpos), Real.rpow_neg (le_of_lt hX0)]
    field_simp
  -- cover the far set by the bands
  have hcover : {p : (ι₁ × ι₂) × ℝ | ∃ k, Mst ≤ |F₁ p.1.1 k - F₂ p.1.2 k|} ⊆
      ⋃ k : ℕ, bandN (Mst * 2 ^ k) F₁ F₂ := by
    intro p hp
    obtain ⟨k₀, hk₀⟩ := hp
    obtain ⟨kmax, -, hkmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun k => |F₁ p.1.1 k - F₂ p.1.2 k|) ⟨k₀, Finset.mem_univ _⟩
    set x := |F₁ p.1.1 kmax - F₂ p.1.2 kmax|
    have hx : Mst ≤ x := le_trans hk₀ (hkmax k₀ (Finset.mem_univ _))
    have h1 : 1 ≤ x / Mst := by rw [le_div_iff₀ hMstpos]; linarith
    obtain ⟨n₀, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1:ℝ) < 2)
    simp only [Set.mem_iUnion]
    refine ⟨n₀, ⟨kmax, ?_⟩, fun k => ?_⟩
    · rw [le_div_iff₀ hMstpos] at hn1; linarith
    · rw [div_lt_iff₀ hMstpos, pow_succ] at hn2
      have := hkmax k (Finset.mem_univ _)
      linarith
  have hsum : Summable (fun k : ℕ => m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) *
      (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hWnn : 0 ≤ ∑ i, T₁ i + ∑ j, T₂ j :=
    add_nonneg (Finset.sum_nonneg (fun i _ => hT₁ i)) (Finset.sum_nonneg (fun j _ => hT₂ j))
  have hCnn : 0 ≤ m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) := by
    have := Real.rpow_nonneg (le_of_lt hX0) (-η₀)
    have := Real.rpow_nonneg (le_of_lt hCpos) η₀
    positivity
  calc P {p | ∃ k, Mst ≤ |F₁ p.1.1 k - F₂ p.1.2 k|}
      = Q {p | ∃ k, Mst ≤ |F₁ p.1.1 k - F₂ p.1.2 k|} :=
        (hQidx {x | ∃ k, Mst ≤ |F₁ x.1 k - F₂ x.2 k|}).symm
    _ ≤ Q (⋃ k : ℕ, bandN (Mst * 2 ^ k) F₁ F₂) := measure_mono hcover
    _ ≤ ∑' k : ℕ, Q (bandN (Mst * 2 ^ k) F₁ F₂) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) *
          (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) := ENNReal.tsum_le_tsum hband
    _ = ENNReal.ofReal (∑' k : ℕ, m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) *
          (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hCnn (pow_nonneg hρ0 k)) hsum).symm
    _ = ENNReal.ofReal (m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) *
          (∑ i, T₁ i + ∑ j, T₂ j) * (1 - ρ)⁻¹) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ ENNReal.ofReal (A * (Mst / δ) ^ (-(η₀ / 4)) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
        apply ENNReal.ofReal_le_ofReal
        have hsplit : (Mst / δ) ^ (-η₀) = (Mst / δ) ^ (-(η₀ / 4)) * (Mst / δ) ^ (-(3 * η₀ / 4)) := by
          rw [← Real.rpow_add hX0]; ring_nf
        have hpos : 0 ≤ A * (Mst / δ) ^ (-(η₀ / 4)) * (∑ i, T₁ i + ∑ j, T₂ j) := by
          have := Real.rpow_nonneg (le_of_lt hX0) (-(η₀ / 4)); positivity
        have hfac : m * 5 ^ n * Crec ^ η₀ * (1 - ρ)⁻¹ * (Mst / δ) ^ (-(3 * η₀ / 4)) ≤ 1 := by
          rw [Real.rpow_neg (le_of_lt hX0), ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hX0 _)]
          refine le_trans ?_ hGX
          rw [hG]
          have h1ρ : 0 < 1 - ρ := by linarith
          rw [← div_eq_mul_inv]
          have hm' : (m:ℝ) ≤ (m:ℝ) + 1 := by linarith
          have h5 : (0:ℝ) ≤ 5 ^ n := by positivity
          have hCe : 0 ≤ Crec ^ η₀ := Real.rpow_nonneg (le_of_lt hCpos) _
          rw [div_le_div_iff_of_pos_right h1ρ]
          calc (m:ℝ) * 5 ^ n * Crec ^ η₀ ≤ ((m:ℝ) + 1) * 5 ^ n * Crec ^ (d + η₀) := by gcongr
            _ = Crec ^ (d + η₀) * ((m:ℝ) + 1) * 5 ^ n := by ring
        calc m * 5 ^ n * A * Crec ^ η₀ * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) * (1 - ρ)⁻¹
            = (A * (Mst / δ) ^ (-(η₀ / 4)) * (∑ i, T₁ i + ∑ j, T₂ j)) *
                (m * 5 ^ n * Crec ^ η₀ * (1 - ρ)⁻¹ * (Mst / δ) ^ (-(3 * η₀ / 4))) := by
              rw [hsplit]; ring
          _ ≤ (A * (Mst / δ) ^ (-(η₀ / 4)) * (∑ i, T₁ i + ∑ j, T₂ j)) * 1 := by gcongr
          _ = _ := mul_one _

end Submission.Obl.k4_horizontal_wide_interval_return.MatchGMLN
