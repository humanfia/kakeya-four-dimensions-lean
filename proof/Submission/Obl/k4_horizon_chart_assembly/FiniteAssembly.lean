import Submission.Obl.k4_horizon_chart_assembly.NativeFamily
import Submission.Obl.k4_horizon_chart_assembly.FiniteMass
import Submission.Obl.k4_horizon_chart_assembly.ParameterScales
import Submission.Obl.k4_horizon_chart_assembly.FinalConversion

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- The supplied kernel gives the complete finite weighted atlas on the
unchanged original priors and incidence events. -/
theorem greedy_finite_weighted_atlas (hker : GreedyKernel) : FiniteWeightedAtlas := by
  classical
  refine ⟨17, 16, by norm_num, by norm_num, ?_⟩
  intro ζ hζ
  obtain ⟨η, C, hη, hC, hgroup⟩ := greedy_group_atlas hker hζ
  refine ⟨η, 1000000 * C, hη, by positivity, ?_⟩
  intro H K hH hK hKH W D₀ ω ν E P B hW hω₀ hω₁ hworld hupper hlower a T
  dsimp only
  intro ha ha1 hqa Dmesh hDmesh hDlarge s τ₀ θ n₀ κ hs hτ hθ hn₀ hκ hsD htrue
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  let S := midpointGroupUniverse q a K
  let I := NativeGroupIndex W T S
  letI : ∀ γ, IsProbabilityMeasure (ν γ) := fun γ => (hworld γ).1
  have hH₀ : 0 ≤ H := by linarith
  have hH₁ : 1 ≤ H := by linarith
  have hK₀ : 0 ≤ K := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hqa' : q ≤ a := by change 8 * q ≤ a at hqa; linarith
  have hDpos : 0 < Dmesh := by omega
  have hκR : 64 * (2 * K + 2) ≤ κ := by linarith
  have hκK : K ≤ κ := by linarith
  have hmesh : 4131 * H * (3 * H + 1) ^ 2 * (q / Dmesh) ≤ a :=
    decoding_mesh_bound hH hq.le hqa hDlarge
  have hP (γ : Fin W) : (P γ).totalDegree ≤ 2 := (hworld γ).2.2.2.2.1
  have hB (γ : Fin W) : 0 < B γ := (hworld γ).2.1
  have hBinv (γ : Fin W) : (B γ)⁻¹ ≤ H := (hworld γ).2.2.2.1
  have hcoeff (γ : Fin W) : ∀ e, |(P γ).coeff e| ≤ H := (hworld γ).2.2.2.2.2.1
  have hE (γ : Fin W) : MeasurableSet (E γ) := (hworld γ).2.2.2.2.2.2.1
  have hunit (γ : Fin W) : E γ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := (hworld γ).2.2.2.2.2.2.2.1
  have hbox (γ : Fin W) : ∀ p ∈ E γ, (p.1.1 : ℝ) ≤ H ∧ ∀ e, |p.1.2 e| ≤ H :=
    (hworld γ).2.2.2.2.2.2.2.2.1
  have hfmt (γ : Fin W) : ∀ i, Fmt 7 H D₀ {z : Fin 7 → ℝ |
      ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ E γ} :=
    (hworld γ).2.2.2.2.2.2.2.2.2
  have hgeo (j : Fin (2 ^ T)) := dyadic_block_geometry T j
  let perGroup := fun g : I => hgroup (ν g.1) (E g.1) (P g.1) K H (B g.1) n₀ (2 * K + 2)
    ((g.2.1 : ℝ) * q) ((g.2.1 : ℝ) * q) q a κ τ₀ s (g.2.1 : ℝ) D₀ T Dmesh
    hK hH₀ (hB g.1) (hP g.1) (hE g.1) (hfmt g.1) (hcoeff g.1)
    hq ha ha1 hqa' rfl rfl le_rfl (hgeo g.2.1).1 (hgeo g.2.1).2.1 (hgeo g.2.1).2.2
    hDmesh hτ hsD hκR hκK htrue g.2.2.val
    (blockGood (ν g.1) (E g.1) (B g.1) a q θ Dmesh g.2.1.val)
    (blockGood_measurable _ _ _ _ _ _ _ _)
    (groupTable (ν g.1) (E g.1) (P g.1) (B g.1) K H a q θ (2 * K + 2) Dmesh g.2.1.val g.2.2.val)
    (groupTable_mem (ν g.1) (hunit g.1) (P g.1) hq hθ (by linarith) hDpos _ _)
  choose m ps cv wv Qv hcount hchart hid hres using perGroup
  have hfamily := native_packet_family S H K τ₀ κ a n₀ ω ν E P B hH hK hτ ha hW hP
    m ps cv wv Qv hcount hchart
  let sel : I → ENNReal := fun g => ∑ i, ((ν g.1).prod volume)
    (nativePacketEvent P B E K H q a g (ps g) i)
  let res : I → Set Trajectory := fun g => packetResidual
    (nativeGroup (P g.1) (B g.1) K H ((g.2.1 : ℝ) * q) q a g.2.2.val)
    (groupIntercept q a ((g.2.1 : ℝ) * q) ((2 * K + 2) * q) g.2.2.val)
    (groupVelocity q ((2 * K + 2) * q)) (ps g)
  let Sel := fun γ : Fin W => extendNativeGroup 0 (fun g => sel (γ, g))
  let Res := fun γ : Fin W => extendNativeGroup ∅ (fun g => res (γ, g))
  have hRes (γ : Fin W) (j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ) :
      Res γ j Γ ⊆ nativeGroup (P γ) (B γ) K H ((j : ℝ) * q) q a Γ := by
    dsimp only [Res, extendNativeGroup]
    split_ifs with hj hΓ
    · exact fun _ hp => hp.1
    · exact empty_subset _
    · exact empty_subset _
  have hid' (γ : Fin W) (j : ℕ) (hj : j ∈ Finset.range (2 ^ T))
      (Γ : (Fin 2 → ℤ) × ℤ) (hΓ : Γ ∈ S) :
      Sel γ j Γ + ENNReal.ofReal q * ((ν γ).prod volume)
        (normalizedEvent (derivativeEvent (E γ) (P γ) (B γ / K)) ((j : ℝ) * q) q ∩
          (Res γ j Γ ×ˢ univ)) =
      ((ν γ).prod volume) (selectedEvent (E γ)
        (nativeGroup (P γ) (B γ) K H ((j : ℝ) * q) q a Γ) (P γ) (B γ / K) ((j : ℝ) * q) q) := by
    simpa only [Sel, Res, extendNativeGroup, dif_pos (Finset.mem_range.mp hj), dif_pos hΓ,
      sel, res, nativePacketEvent, nativePacketSet] using
      hid (γ, ⟨j, Finset.mem_range.mp hj⟩, ⟨Γ, hΓ⟩)
  have hres' (γ : Fin W) (j : ℕ) (hj : j ∈ Finset.range (2 ^ T))
      (Γ : (Fin 2 → ℤ) × ℤ) (hΓ : Γ ∈ S) :=
    hres (γ, ⟨j, Finset.mem_range.mp hj⟩, ⟨Γ, hΓ⟩)
  have hworldmass (γ : Fin W) := world_mass_balance (ν γ) (hE γ) (hunit γ) (P γ) (hP γ)
    (R := 2 * K + 2) (C := C) (τ₀ := τ₀) (σ := s) (ζ := ζ)
    (hB γ) hK₀ hH₁ (hcoeff γ) (hBinv γ) (hbox γ) (hupper γ) (hlower γ)
    ha ha1 hqa' hθ hDpos hmesh hs hC.le hτ.le rfl (Sel γ) (Res γ) (hRes γ) (hid' γ)
    (by
      intro j hj Γ hΓ
      change Γ ∈ S at hΓ
      simpa only [Res, extendNativeGroup, dif_pos (Finset.mem_range.mp hj), dif_pos hΓ, res] using
        hres' γ j hj Γ hΓ)
  let SelWorld := fun γ : Fin W => ∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ S, Sel γ j Γ
  have hweighted := weighted_world_mass_balance ω ν E B a q θ s
    (4 * nativeMultiplicity K * C * τ₀ * (Dmesh : ℝ) ^ ζ / (s * θ * q ^ 2)) SelWorld
    hω₀ hω₁ hworldmass
  have hSelSum : (∑ γ, ENNReal.ofReal (ω γ) * SelWorld γ) =
      ∑ g : I, ∑ i, ENNReal.ofReal (ω g.1) * ((ν g.1).prod volume)
        (nativePacketEvent P B E K H q a g (ps g) i) := by
    dsimp only [I, NativeGroupIndex]
    simp only [SelWorld, Sel, sum_extendNativeGroup, Fintype.sum_prod_type, sel, Finset.mul_sum]
  have hL : 4 * nativeMultiplicity K * C ≤ 1000000 * C * K ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right (nativeMultiplicity_le hK) (show 0 ≤ 4 * C by positivity)
    nlinarith [mul_nonneg hC.le (pow_nonneg hK₀ 3)]
  have hfactor : 4 * nativeMultiplicity K * C * τ₀ * (Dmesh : ℝ) ^ ζ / (s * θ * q ^ 2) ≤
      (1000000 * C) * K ^ 3 * τ₀ * (Dmesh : ℝ) ^ ζ / (s * θ * q ^ 2) := by
    gcongr
  obtain ⟨C', γ, j, c, u, Q, R, A', F, hcount', hdisj, hchart', hselected⟩ := hfamily
  refine ⟨C', γ, j, c, u, Q, R, A', F, hcount', hdisj, ?_, ?_⟩
  · intro b
    change RawChart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact rawChart_mono le_rfl le_rfl (hchart' b) (fun hb => by
      have heq : n₀ * ((2 : ℝ) ^ T)⁻¹ * |(Q b).det| / κ =
          n₀ * |(Q b).det| / ((2 : ℝ) ^ T * κ) := by ring
      simpa only [heq] using hb)
  · rw [hSelSum] at hweighted
    exact hweighted.trans (add_le_add
      (add_le_add (add_le_add hselected le_rfl) le_rfl)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) le_rfl))

end
end Submission.Obl.k4_horizon_chart_assembly
