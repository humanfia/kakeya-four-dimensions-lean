-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoverMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FiberMass
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FiberRefinement

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set

/-- Positive density and balanced fine fibers turn a retained mass bound into a retained
coarse cardinality bound. No comparability of the individual shading masses is assumed. -/
theorem retained_cover_card_bound {δ η h τ m l ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : A δ η m l n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f) (Q : Finset (Fin N))
    (hkeep : o (δ ^ τ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S with f i ∈ Q, μ (Z i)) :
    δ ^ (τ + η + h) * N ≤ 384 * Q.card := by
  classical
  have hYtop (i) : μ (Y i) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1))
      (measure_ball_lt_top : volume (Metric.ball (0 : V) 1) < ⊤)).ne
  have hZbound (i) : μ (Z i) ≤ o (384 * δ ^ 2) :=
    (measure_mono ((hC.1 i).2.1.trans (hA.2.1 i).2.2.2)).trans
      (tube_volume_upper hδ hδ1 (x i) (v i) (hA.2.1 i).1)
  have hZtop (i) : μ (Z i) ≠ ⊤ := (lt_of_le_of_lt (hZbound i) ENNReal.ofReal_lt_top).ne
  have hdense : (δ ^ η * δ ^ 2) * (n : ℝ) ≤ ∑ i, (μ (Y i)).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hYtop i)) hA.2.2.2.1
    change (o (δ ^ η * n * δ ^ 2)).toReal ≤ _ at hh
    rw [o, ENNReal.toReal_ofReal (by positivity : 0 ≤ δ ^ η * n * δ ^ 2),
      ENNReal.toReal_sum (fun i _ => hYtop i)] at hh
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hkeep' : δ ^ τ * (∑ i, (μ (Y i)).toReal) ≤
      ∑ i ∈ S with f i ∈ Q, (μ (Z i)).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hZtop i)) hkeep
    simpa only [o, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
      ENNReal.toReal_sum (fun i _ => hYtop i),
      ENNReal.toReal_sum (fun i _ => hZtop i)] using hh
  have hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      δ ^ (-h) * (S.filter (fun i => f i = k')).card := by
    intro k k'
    have hh := hC.2.2.2.2.2.2.1 k k'
    simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hh
  have hweights (i) (_hi : i ∈ S) : (μ (Z i)).toReal ≤ 384 * δ ^ 2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hZbound i)
    simpa only [o, ENNReal.toReal_ofReal (by positivity : 0 ≤ 384 * δ ^ 2)] using hh
  have hc := selected_fiber_card_of_mass S Q f (fun i => (μ (Z i)).toReal)
    (Real.rpow_nonneg hδ.le τ) (by positivity : 0 ≤ 384 * δ ^ 2)
    (Real.rpow_nonneg hδ.le (-h)) (by simpa using hA.1) hweights hbal
    (by simpa using hdense) (by simpa using hkeep')
  simp only [Fintype.card_fin] at hc
  have hc' : (δ ^ τ * δ ^ η * N) * δ ^ 2 ≤
      (384 * δ ^ (-h) * Q.card) * δ ^ 2 := by nlinarith [hc]
  have hc'' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp hc'
  calc
    δ ^ (τ + η + h) * N = δ ^ h * (δ ^ τ * δ ^ η * N) := by
      rw [Real.rpow_add hδ, Real.rpow_add hδ]
      ring
    _ ≤ δ ^ h * (384 * δ ^ (-h) * Q.card) :=
      mul_le_mul_of_nonneg_left hc'' (Real.rpow_nonneg hδ.le h)
    _ = 384 * Q.card := by
      have he : δ ^ h * δ ^ (-h) = 1 := by rw [← Real.rpow_add hδ]; simp
      calc
        _ = 384 * (δ ^ h * δ ^ (-h)) * Q.card := by ring
        _ = _ := by rw [he, mul_one]

/-- The normalized Frostman loss is bounded solely by the mass retention and density errors. -/
theorem frostman_loss_of_card_bound {δ η h τ : ℝ} {N M : ℕ}
    (hδ : 0 < δ) (hM : 0 < M)
    (hcard : δ ^ (τ + η + h) * N ≤ 384 * M) :
    δ ^ (-h) * N / M ≤ 384 * δ ^ (-(τ + η + 2 * h)) := by
  have hM' : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  apply (div_le_iff₀ hM').mpr
  have hpow : δ ^ (-(τ + η + 2 * h)) * δ ^ (τ + η + h) = δ ^ (-h) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  calc
    δ ^ (-h) * N = δ ^ (-(τ + η + 2 * h)) * (δ ^ (τ + η + h) * N) := by
      rw [← mul_assoc, hpow]
    _ ≤ δ ^ (-(τ + η + 2 * h)) * (384 * M) :=
      mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg hδ.le _)
    _ = (384 * δ ^ (-(τ + η + 2 * h))) * M := by ring

/-- A coarse restriction retaining mass gives the refinement alternative; the exponent
budget explicitly pays for the change in Frostman normalization. -/
theorem refined_of_retained_cover {ζ δ ρ η h τ m l : ℝ} {n N M : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτζ : τ ≤ ζ) (hhζ : h ≤ ζ)
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (hM : 0 < M) (e : Fin M → Fin N) (he : Function.Injective e)
    (hK : K ρ (δ ^ (-ζ)) M (y ∘ e) (w ∘ e))
    (hbudget : 384 * δ ^ (-(τ + η + 2 * h)) ≤ δ ^ (-ζ))
    (hkeep : o (δ ^ τ) * ∑ i, μ (Y i) ≤
      ∑ i ∈ S with f i ∈ Set.range e, μ (Z i)) :
    Refined ζ δ ρ n x v Y S Z := by
  classical
  let Q : Finset (Fin N) := Finset.univ.image e
  have hQ : (↑Q : Set (Fin N)) = Set.range e := by ext k; simp [Q]
  have hQcard : Q.card = M := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_image_of_injective Finset.univ he
  have hcard : δ ^ (τ + η + h) * N ≤ 384 * M := by
    rw [← hQcard]
    apply retained_cover_card_bound hδ hδ1 hA hC Q
    simpa only [← hQ, Finset.mem_coe] using hkeep
  refine refined_of_selected_cover hC hM e he hK
    ((frostman_loss_of_card_bound hδ hM hcard).trans hbudget)
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhζ)) ?_
  apply le_trans _ hkeep
  exact mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hτζ)) _

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
