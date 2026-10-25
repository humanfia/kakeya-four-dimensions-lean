import Submission.Obl.k4_scalar_crop_profile_transport.Pure
import Submission.Obl.k4_scalar_crop_profile_transport.LabelTail

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set
open scoped ENNReal

local instance : SigmaFinite BaseRef := by unfold BaseRef; infer_instance
local instance : SigmaFinite JointRef := by unfold JointRef; infer_instance

lemma scalar_upper_scaling_iff {a p δ : ℝ} (ha : 0 < a) (hp : 0 < p) (hδ : 0 < δ)
    (hi : ℝ) (v : ENNReal) :
    (ENNReal.ofReal ((a / p) * hi / δ) < v) ↔
      ENNReal.ofReal hi < ENNReal.ofReal δ * ((ENNReal.ofReal p / ENNReal.ofReal a) * v) := by
  have hw : (ENNReal.ofReal (hi / δ) < (ENNReal.ofReal p / ENNReal.ofReal a) * v) ↔
      ENNReal.ofReal ((a / p) * (hi / δ)) < v := by
    simpa only [mul_zero, ENNReal.ofReal_zero, not_lt_zero, false_or] using
      raw_window_iff ha hp v 0 (hi / δ) 1
  rw [show (a / p) * hi / δ = (a / p) * (hi / δ) by ring, ← hw,
    ENNReal.ofReal_div_of_pos hδ,
    ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hδ))
      (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm (ENNReal.ofReal δ)]

open Classical in
/-- The finite scalar angular tail follows from its raw observation law and a
bounded relation between the original and shifted velocity labels. -/
theorem finite_angular_from_raw (N L u₀ u : ℝ) (hN : 0 < N)
    (μ₀ : Measure Inc) [IsFiniteMeasure μ₀] (hmass : μ₀ univ ≤ 1)
    (w : ℕ) (p : Fin w → ℝ) (z : Fin w → Fin 2 → ℤ)
    (μ : Fin w → Measure Inc) (G : Fin w → Joint → ENNReal)
    (hp : ∀ γ, 0 < p γ) (hG : ∀ γ, Measurable (G γ))
    (hlift : ∀ γ Z, MeasurableSet Z → ENNReal.ofReal (p γ) * μ γ Z =
      μ₀ {q | q.1 ∈ Cell (N ^ (-u₀)) (z γ) ∧ CropInc (N ^ (-u₀)) (z γ) q ∈ Z})
    (hdisj : Pairwise fun γ γ' => Disjoint (Cell (N ^ (-u₀)) (z γ))
      (Cell (N ^ (-u₀)) (z γ')))
    (t : Fin w → Inc → ℤ) (ht : ∀ γ, Measurable (t γ))
    (hcomm : ∀ γ q, Aug N L u (CropInc (N ^ (-u₀)) (z γ) q) =
      (obsEquiv (N ^ (-u₀)) (Real.rpow_pos_of_pos hN _).ne' (z γ) (Obs N L q), t γ q))
    (htarget : ∀ γ, (μ₀.restrict (Cell (N ^ (-u₀)) (z γ) ×ˢ univ)).map
        (fun q => (Obs N L q, t γ q)) = JointRef.withDensity
      (fun b => (ENNReal.ofReal (p γ) / ENNReal.ofReal (N ^ (-u₀))) *
        G γ (obsEquiv (N ^ (-u₀)) (Real.rpow_pos_of_pos hN _).ne' (z γ) b.1, b.2)))
    (H : Joint → ENNReal) (hH : Measurable H)
    (hsource : μ₀.map (Aug N L (u₀ + u)) = JointRef.withDensity H)
    (R : Fin w → ℤ → ℤ → Prop)
    (hR : ∀ γ, ∀ᵐ q ∂μ₀.restrict (Cell (N ^ (-u₀)) (z γ) ×ˢ univ),
      R γ (⌊q.1.2 1 / N ^ (-(u₀ + u))⌋) (t γ q))
    (hcard : ∀ γ j, ∑' i, (if R γ i j then (1 : ENNReal) else 0) ≤ 2)
    (hi δ : ℝ) (hδ : 0 < δ) :
    (∑ γ, ENNReal.ofReal (p γ) * μ γ
      {q | ENNReal.ofReal ((N ^ (-u₀) / p γ) * hi / δ) < G γ (Aug N L u q)}) ≤
      μ₀ {q | ENNReal.ofReal hi < H (Aug N L (u₀ + u) q)} + ENNReal.ofReal (32 * δ) := by
  classical
  let a := N ^ (-u₀)
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  let S : Fin w → Set Inc := fun γ => Cell a (z γ) ×ˢ univ
  let s : Inc → ℤ := fun q => ⌊q.1.2 1 / N ^ (-(u₀ + u))⌋
  let D : Fin w → Joint → ENNReal := fun γ b =>
    (ENNReal.ofReal (p γ) / ENNReal.ofReal a) * G γ (obsEquiv a ha.ne' (z γ) b.1, b.2)
  have hS (γ : Fin w) : MeasurableSet (S γ) := (measurableSet_Cell _ _).prod MeasurableSet.univ
  have hs : Measurable s := by unfold s; fun_prop
  have hD (γ : Fin w) : Measurable (D γ) :=
    measurable_const.mul ((hG γ).comp
      (((obsEquiv a ha.ne' (z γ)).measurable.comp measurable_fst).prodMk measurable_snd))
  have hpart : ∀ γ, ∃ Hγ : Joint → ENNReal, Measurable Hγ ∧
      (μ₀.restrict (S γ)).map (Aug N L (u₀ + u)) = JointRef.withDensity Hγ := by
    intro γ
    exact k4_crop_angular_finite_tail.exists_density_of_le JointRef
      Measure.restrict_le_self (measurable_Aug N L (u₀ + u)) hsource
  choose Hpart hHpart hpart using hpart
  have hdisjS : Pairwise fun γ γ' => Disjoint (S γ) (S γ') := by
    intro γ γ' hne
    apply Set.disjoint_left.mpr
    intro q hq hq'
    exact Set.disjoint_left.mp (hdisj hne) hq.1 hq'.1
  have htail := restricted_label_upper_tail BaseRef μ₀ (Obs N L) (measurable_Obs N L)
    s hs t ht S hS hdisjS H hH hsource Hpart hHpart hpart D hD htarget R hR 2 hcard
    (ENNReal.ofReal δ) (ENNReal.ofReal hi)
  have hleft (γ : Fin w) : ENNReal.ofReal (p γ) * μ γ
      {q | ENNReal.ofReal ((a / p γ) * hi / δ) < G γ (Aug N L u q)} =
      (μ₀.restrict (S γ)) {q | ENNReal.ofReal hi < ENNReal.ofReal δ * D γ (Obs N L q, t γ q)} := by
    have hbad : MeasurableSet {q | ENNReal.ofReal ((a / p γ) * hi / δ) < G γ (Aug N L u q)} :=
      measurableSet_lt measurable_const ((hG γ).comp (measurable_Aug N L u))
    have hrawbad : MeasurableSet {q | ENNReal.ofReal hi < ENNReal.ofReal δ * D γ (Obs N L q, t γ q)} :=
      measurableSet_lt measurable_const
        (measurable_const.mul ((hD γ).comp ((measurable_Obs N L).prodMk (ht γ))))
    rw [hlift γ _ hbad, Measure.restrict_apply hrawbad]
    apply congrArg μ₀
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, S]
    rw [hcomm]
    change (q.1 ∈ Cell a (z γ) ∧ _ ) ↔ (_ ∧ q.1 ∈ Cell a (z γ))
    rw [and_comm]
    exact and_congr_left fun _ => scalar_upper_scaling_iff ha (hp γ) hδ hi _
  calc
    _ = ∑ γ, (μ₀.restrict (S γ))
      {q | ENNReal.ofReal hi < ENNReal.ofReal δ * D γ (Obs N L q, t γ q)} :=
      Finset.sum_congr rfl fun γ _ => hleft γ
    _ ≤ μ₀ {q | ENNReal.ofReal hi < H (Aug N L (u₀ + u) q)} +
        ENNReal.ofReal δ * 2 * μ₀ univ := htail
    _ ≤ μ₀ {q | ENNReal.ofReal hi < H (Aug N L (u₀ + u) q)} + ENNReal.ofReal (32 * δ) := by
      gcongr
      calc
        ENNReal.ofReal δ * 2 * μ₀ univ ≤ ENNReal.ofReal δ * 2 * 1 := mul_le_mul' le_rfl hmass
        _ = ENNReal.ofReal (2 * δ) := by rw [mul_one, mul_comm, ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ ENNReal.ofReal (32 * δ) := ENNReal.ofReal_le_ofReal (by linarith)

end Submission.Obl.k4_scalar_crop_profile_transport
