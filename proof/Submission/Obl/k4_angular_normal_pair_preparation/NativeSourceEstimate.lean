import Submission.Obl.k4_angular_normal_pair_preparation.NormalException
import Submission.Obl.k4_angular_normal_pair_preparation.ChargeBridge
import Submission.Obl.k4_angular_normal_pair_preparation.DyadicFacts
import Submission.Obl.k4_angular_normal_pair_preparation.Conclusion

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace NativeSample

/-- Bound one discarded row by the unchanged terminal/angular law at its witness time. -/
theorem source_badRow_le
    {aligned : Prop} {lam Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ} {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S A R e h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}
    (q : NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S (A * e) e (R * e)
      h M D depths ε)
    (hf : SampleFacts Wk ωk νk Ek Bk) (hN : 0 < Nk)
    (hGm : ∀ γ₀, Measurable (Gk γ₀ (R * e)))
    (hGmap : ∀ γ₀, Measure.map (angObs (Bk γ₀) (δ Nk L) (δ Nk (R * e)))
      (((νk γ₀).prod volume).restrict (Ek γ₀)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (Gk γ₀ (R * e)))
    (b : Fin q.C) :
    ((νk (q.γ b)).prod (volume.prod volume)) (q.badRow (R * e) b) ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ (q.T + q.s)) *
        ENNReal.ofReal (Nk ^ (-f L - S * (R * e) + A * e) *
          ((1 / (2 : ℝ) ^ q.T) *
            (nativeGeometryLoss q.κ ((2 : ℝ) ^ q.s) (Nk ^ (2 * A * e)) * |(q.Q b).det|))) := by
  classical
  letI := hf.prior_prob
  by_cases hiso : q.R₁ ≤ 8 * Nk ^ (R * e) * q.R₂
  · have hempty : q.badRow (R * e) b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro p ⟨b', _, hbad⟩
      exact hbad (Or.inl hiso)
    rw [hempty, measure_empty]
    exact bot_le
  have hκ : 0 < q.κ := zero_lt_one.trans_le q.κ_one
  have hR₁ : 0 < q.R₁ := q.R₂_pos.trans_le q.R₂_le
  have hδL : 0 < δ Nk L := (delta_bounds hN L).1
  have hδu : 0 < δ Nk (R * e) := (delta_bounds hN (R * e)).1
  let q₀ : ℝ := (2 : ℝ) ^ (q.T + q.s)
  let q₁ : ℝ := (2 : ℝ) ^ q.T
  have hq₀ : 0 < q₀ := by positivity
  have hq₁ : 0 < q₁ := by positivity
  let t₀ : ℝ := (((q.j b : ℕ) / 2 ^ q.s : ℕ) : ℝ) / q₁
  let ℓ : ℝ := 1 / q₁
  let δL := δ Nk L
  let δu := δ Nk (R * e)
  let width := δL * Nk ^ (A * e)
  let β := Bk (q.γ b) * Nk ^ (-(A * e))
  let ρ := 32 * q.κ ^ 2 * δu
  let cap := Nk ^ (-f L - S * (R * e) + A * e)
  let angle := Nk ^ (R * e) * q.R₂ / q.R₁
  have hangle : 0 < angle := by
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hN _) q.R₂_pos) hR₁
  have hmesh : min (1 / 8 : ℝ) (Nk ^ (R * e) * q.R₂ / q.R₁) = angle := by
    apply min_eq_right
    apply (div_le_iff₀ hR₁).mpr
    push Not at hiso
    linarith
  let Exc : Fin q.C → Prop := fun b' => ¬q.Alignment (R * e) b b'
  let V : Fin q.C → Set (EuclideanSpace ℝ (Fin 2)) := fun b' =>
    velEllipse q.κ (q.T + q.s) (q.v₀ b) (q.Q b) ∩
      velEllipse q.κ (q.T + q.s) (q.v₀ b') (q.Q b')
  have hVm : ∀ b', MeasurableSet (V b') := by
    have hsingle (c : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
        MeasurableSet (velEllipse q.κ (q.T + q.s) c Q) := by
      have hc : Continuous (fun w : EuclideanSpace ℝ (Fin 2) =>
          ‖Matrix.toEuclideanLin Q⁻¹ (w - c)‖) :=
        ((LinearMap.continuous_of_finiteDimensional _).comp
          (continuous_id.sub continuous_const)).norm
      exact measurableSet_le hc.measurable measurable_const
    exact fun b' => (hsingle _ _).inter (hsingle _ _)
  have htimeScale : q₀ * q.R₁ ≤ q.κ := by
    have hh := ((q.classes b).1.trans (r₁_le_entrySum _)).trans (q.charts b).2.2.2.1
    have hh' := (le_div_iff₀ hq₀).mp hh
    nlinarith
  have hball : ∀ b', ∃ w : EuclideanSpace ℝ (Fin 2),
      Exc b' → V b' ⊆ Metric.closedBall w ρ := by
    intro b'
    by_cases hb' : Exc b'
    · have hsep : angle ≤ |wedge (nrm (q.Q b)) (nrm (q.Q b'))| := by
        apply le_of_lt
        apply lt_of_not_ge
        intro hle
        exact hb' (Or.inr (by rwa [hmesh]))
      obtain ⟨w, hw⟩ := velocity_inter_subset_ball (q.charts b).1 (q.charts b').1
        (u := q.v₀ b) (u' := q.v₀ b') (W := 2 * q.κ * q₀) hangle hsep
      refine ⟨w, fun _ => hw.trans (Metric.closedBall_subset_closedBall ?_)⟩
      exact transverse_radius_le hN hκ.le hq₀.le hR₁ q.R₂_pos htimeScale
        (q.classes b).2.2.2.le (q.classes b').2.2.2.le
        (show (q.R₂ / q.R₁) * Nk ^ (R * e) ≤ angle by dsimp [angle]; exact le_of_eq (by ring))
        (delta_bounds hN (R * e)).2.1
    · exact ⟨0, fun hb => (hb' hb).elim⟩
  choose center hcenter using hball
  obtain ⟨hdet, _, _, _, hdegree, _, hAm, _, _, hline, hsel, _⟩ := q.charts b
  have hleft : t₀ ≤ ((q.j b : ℕ) : ℝ) / q₀ := (fine_coarse_endpoints q.T q.s (q.j b)).1
  have hright : (((q.j b : ℕ) : ℝ) + 1) / q₀ ≤ t₀ + ℓ := by
    convert (fine_coarse_endpoints q.T q.s (q.j b)).2 using 1 <;> dsimp [t₀, ℓ, q₀, q₁] <;> ring
  have hcoarse : coarseInterval q.T q.s (q.j b) = Icc t₀ (t₀ + ℓ) := by
    dsimp [coarseInterval, t₀, ℓ, q₁]
    congr 1
    ring
  have hlstm := measurableSet_list_of_incidence_membership (hf.scale_pos (q.γ b)).ne'
    hδL.ne' (q.lst (q.γ b)) (fun i => (q.list_format (q.γ b) i).1)
  let J : Fin q.C → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) := fun b' =>
    {p | (p.1, p.2.1) ∈ q.F b ∧
      (p.1, p.2.2) ∈ excIncidences (q.A b) t₀ ℓ (q.R b) width β (Bk (q.γ b)) δL
        (q.lst (q.γ b)) b' (V b') ∧
      (p.1, p.2.2) ∈ Ek (q.γ b) ∧
      Gk (q.γ b) (R * e) (angObs (Bk (q.γ b)) δL δu (p.1, p.2.2)) ≤ ENNReal.ofReal cap}
  have hsub : q.badRow (R * e) b ⊆ ⋃ b' : {b' // Exc b'}, J b' := by
    rintro p ⟨b', hp, hbad⟩
    apply mem_iUnion.mpr
    refine ⟨⟨b', hbad⟩, ?_⟩
    obtain ⟨hγ, hj, hF, hF', _, hGood', hder, _⟩ := (q.pairs b b').2 p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, hline', hsel', hex'⟩ := q.charts b'
    have hA := (hsel _ hF).2.1
    have hA' := (hsel' _ hF').2.1
    have ht' := fine_subset_coarse q.T q.s (q.j b') (hsel' _ hF').2.2.1
    have ht : p.2.2 ∈ coarseInterval q.T q.s (q.j b) := by
      simpa only [coarseInterval, hj] using ht'
    have htI : p.2.2 ∈ Icc t₀ (t₀ + ℓ) := by rwa [← hcoarse]
    have hwhole := q.whole b p.1 hA p.2.2 ht
    have hlist := hex'.2 (p.1, p.2.2) hF'
    rw [← hγ] at hlist
    refine ⟨hF, ⟨hA, htI, hwhole.2.1,
      hder (q.R b) (Or.inl rfl) p.2.2 (Or.inr rfl), hlist, ?_⟩,
      (q.good (q.γ b)).2.1 hGood', ((q.good (q.γ b)).2.2 _ hGood').2.2.2.2⟩
    exact ⟨v_mem_velEllipse (fun t ht => ((hline p.1 hA).2.2 t ht).1),
      v_mem_velEllipse (fun t ht => ((hline' p.1 hA').2.2 t ht).1)⟩
  have hrow : ((νk (q.γ b)).prod (volume.prod volume)) (q.badRow (R * e) b) ≤
      ∑ b' : {b' // Exc b'}, ((νk (q.γ b)).prod (volume.prod volume)) (J b') := by
    apply (measure_mono hsub).trans
    exact measure_iUnion_fintype_le _ _
  have hk := source_exceptional_pairs (ι := Fin q.C) (κ := q.κ)
    (j₀ := ((q.j b : ℕ) : ℝ)) (a := t₀) (ℓ := ℓ) (ε := width) (β := β)
    (ρ := ρ) (H := q.κ) (cap := cap) (T₀ := q.T + q.s)
    (νk (q.γ b)) (Ek (q.γ b)) (hf.event_meas _) (Gk (q.γ b) (R * e))
    (hf.scale_pos _) hδL hδu (hGm _) (hGmap _) hκ.le (by positivity)
    (by dsimp [β]; exact mul_pos (hf.scale_pos _) (Real.rpow_pos_of_pos hN _))
    (by positivity) hκ.le (Real.rpow_nonneg hN.le _) (q.c b) (q.v₀ b) (q.Q b) hdet
    (q.R b) hdegree (q.A b) hAm
    (fun l hl t ht => ((hline l hl).2.2 t ht).1) hleft hright (q.F b)
    (fun p hp => (hsel p hp).2.2.1) (q.lst (q.γ b)) (q.list_card (q.γ b)) hlstm
    Exc V hVm center hcenter
  have hscale : q.κ + 2 * q.κ * (2 : ℝ) ^ (q.T + q.s) * ℓ =
      q.κ + 2 * q.κ * (2 : ℝ) ^ q.s := by
    dsimp [ℓ, q₁]
    rw [pow_add]
    field_simp
  have hhidden : width / (β * (δL / Bk (q.γ b))) = Nk ^ (2 * A * e) := by
    dsimp [width, β]
    rw [native_hidden_ratio hN hδL.ne' (hf.scale_pos _).ne']
    congr 1
    ring
  have hvelocity : 4 * ρ / δu + 2 = 128 * q.κ ^ 2 + 2 := by
    dsimp [ρ]
    field_simp [show δu ≠ 0 from hδu.ne']
    ring
  apply (hrow.trans hk).trans_eq
  simp only [one_div]
  congr 1
  congr 1
  rw [hscale, hhidden, hvelocity]
  dsimp [cap, nativeGeometryLoss, ℓ, q₁]
  ring

end NativeSample

/-- The exact finite analytic estimate needed by the final cofinal argument. -/
theorem normal_point_estimate (A S R : ℝ) (hA : 0 < A) (hS : 0 < S)
    (hR : 3 * A + 20 ≤ S * R) : NormalPointEstimate A S R := by
  intro N K L d η W ω ν E P B f g G hp h e he hu M D depths ε hε hεe k hlarge q
  have hRpos : 0 < R := by nlinarith
  let hf := prob_sampleFacts hp k
  apply q.badMass_le_of_source_bounds hf (by linarith [prob_N_ge hp k])
    hA.le he.le hεe hlarge hR
  apply q.source_badRow_le hf (by linarith [prob_N_ge hp k])
  · exact fun γ₀ => (prob_angular_law hp k γ₀ (R * e) (mul_pos hRpos he) hu).1
  · exact fun γ₀ => (prob_angular_law hp k γ₀ (R * e) (mul_pos hRpos he) hu).2

/-- Angular normal preparation with unchanged original laws and native chart data. -/
theorem normal_preparation : NormalPreparationStatement :=
  normal_preparation_of_pointEstimate normal_point_estimate

end Submission.Obl.k4_angular_normal_pair_preparation
