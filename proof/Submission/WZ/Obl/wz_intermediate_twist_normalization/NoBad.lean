-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.NoBad.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Saturate
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Core

/-!
# The black box applied to one class

`GBeAt ε η d0 C` is the statement of `GBe` for fixed parameters. `class_bound` applies it to
the normalized tubes of a class `J` (all satisfying `CG`), with the saturations of the parts
of the shadings lying over a measurable planar set `G` and inside the height windows. If these
parts carry mass at least `200 ρ^η' |J| δ²`, the zoomed area of `G` is at least
`ρ^ε |J| / (C Kt)` with the inherited count coefficient `Kt = δ^(-η) n / Z²`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj CountF)

/-- The statement of `GBe` for fixed parameters. -/
def GBeAt (ε η d0 C : ℝ) : Prop :=
  ∀ ρ r e : ℝ, 0 < ρ → ρ ≤ d0 → ρ ^ η ≤ r → 16 * r ^ 2 ≤ e → e ≤ 1 / 4 →
  ∀ (m : ℕ) (x v : Fin m → Space) (Y : Fin m → Set Space) (Kt : ℝ), 0 < m →
    (∀ i, ‖v i‖ = 1) → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
    (∀ i, tube ρ (x i) (v i) ⊆ safeCyl r e) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube ρ (x i) (v i)) →
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube ρ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W))) →
    ENNReal.ofReal (ρ ^ η * (m : ℝ) * ρ ^ 2) ≤ ∑ i, volume (Y i) →
    ∀ f : ℝ → ℝ, SlopeN f → f 0 = 0 →
    ENNReal.ofReal (ρ ^ ε * (m : ℝ)) ≤ ENNReal.ofReal (C * Kt) * volume (proj f (⋃ i, Y i))

theorem GBe.exists_at (h : GBe) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∃ C : ℝ, 0 < C ∧ GBeAt ε η d0 C :=
  h ε hε

/-- Smaller exponents `η` give stronger hypotheses. -/
theorem GBeAt.mono {ε η d0 C η' : ℝ} (h : GBeAt ε η d0 C) (hη' : 0 < η') (hle : η' ≤ η) :
    GBeAt ε η' (min d0 1) C := by
  intro ρ r e hρ hρd hρr he16 he4 m x v Y Kt hm hv hv2 hT hYm hYT hcount hmass f hf hf0
  have hρ1 : ρ ≤ 1 := hρd.trans (min_le_right _ _)
  have hpow : ρ ^ η ≤ ρ ^ η' := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hle
  refine h ρ r e hρ (hρd.trans (min_le_left _ _)) (hpow.trans hρr) he16 he4 m x v Y Kt hm hv hv2
    hT hYm hYT hcount ?_ f hf hf0
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
  have : 0 ≤ (m : ℝ) * ρ ^ 2 := by positivity
  nlinarith

/-- The centred slope function satisfies the slope hypothesis. -/
theorem slopeN_centred {f : ℝ → ℝ} (hf : SlopeN f) : SlopeN (fun w => f w - f 0) := by
  refine ⟨hf.1.sub contDiff_const, fun z hz => ?_⟩
  have hd : deriv (fun w => f w - f 0) = deriv f := funext fun w => deriv_sub_const _
  rw [hd]
  exact hf.2 z hz

/-- The part of a shading used for a class. -/
def clPart (f : ℝ → ℝ) (Z β ρ e δ : ℝ) (G : Set (ℝ × ℝ)) (x v : Space) (Y : Set Space) :
    Set Space :=
  Y ∩ pmap f ⁻¹' G ∩ nwin Z (f 0) β ρ e δ x v

theorem measurableSet_clPart {f : ℝ → ℝ} (hf : Continuous f) (Z β ρ e δ : ℝ)
    {G : Set (ℝ × ℝ)} (hG : MeasurableSet G) (x v : Space) {Y : Set Space}
    (hY : MeasurableSet Y) : MeasurableSet (clPart f Z β ρ e δ G x v Y) :=
  (hY.inter (hG.preimage (continuous_pmap hf).measurable)).inter (measurableSet_nwin _ _ _ _ _ _ _ _)

/-- **The black box on one class.** -/
theorem class_bound {εG ηG dG CG' : ℝ} (hGB : GBeAt εG ηG dG CG')
    {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hF : CountF η δ n x v) {f : ℝ → ℝ} (hf : SlopeN f)
    {Z ρ e r0 α β : ℝ} (J : Finset (Fin n)) (hJ : J.Nonempty)
    (hCG : ∀ j ∈ J, CG (f 0) δ Z ρ e r0 α β (x j) (v j))
    (hρd : ρ ≤ dG) (hρr : ρ ^ ηG ≤ r0)
    {G : Set (ℝ × ℝ)} (hGm : MeasurableSet G)
    (hmass : ENNReal.ofReal (200 * ρ ^ ηG * (J.card : ℝ) * δ ^ 2) ≤
      ∑ j ∈ J, volume (clPart f Z β ρ e δ G (x j) (v j) (Y j))) :
    ENNReal.ofReal (ρ ^ εG * (J.card : ℝ)) ≤
      ENNReal.ofReal (CG' * (δ ^ (-η) * n / Z ^ 2)) * (ENNReal.ofReal Z * volume G) := by
  classical
  obtain ⟨j0, hj0⟩ := hJ
  have h0 := hCG j0 hj0
  have hZ := h0.hZ
  have hδ := h0.hδ
  have hc := h0.hc
  have hρ0 : 0 < ρ := by rw [h0.hρ]; positivity
  have hfc : Continuous f := hf.continuous
  set m := J.card with hmdef
  have hm : 0 < m := Finset.card_pos.mpr ⟨j0, hj0⟩
  let eJ : Fin m ≃ { j // j ∈ J } := J.equivFin.symm
  let g : Fin m → Fin n := fun i => (eJ i : Fin n)
  have hgJ : ∀ i, g i ∈ J := fun i => (eJ i).2
  have hg_inj : Function.Injective g := fun i i' h => eJ.injective (Subtype.ext h)
  set A : Fin n → Set Space := fun j => clPart f Z β ρ e δ G (x j) (v j) (Y j) with hAdef
  set x' : Fin m → Space := fun i => nbase Z (f 0) α β ρ e (x (g i)) (v (g i)) with hx'
  set v' : Fin m → Space := fun i => ndir Z (f 0) β (v (g i)) with hv'
  set Y' : Fin m → Set Space := fun i => nsat f Z α β ρ e (x (g i)) (v (g i)) (A (g i)) with hY'
  set Kt : ℝ := δ ^ (-η) * n / Z ^ 2 with hKt
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    measurableSet_clPart hfc Z β ρ e δ hGm (x j) (v j) (hYm j)
  have hAsub : ∀ j, A j ⊆ tube δ (x j) (v j) ∩ nwin Z (f 0) β ρ e δ (x j) (v j) :=
    fun j p hp => ⟨hYT j hp.1.1, hp.2⟩
  -- the hypotheses of the black box
  have hunit : ∀ i, ‖v' i‖ = 1 := fun i => (hCG _ (hgJ i)).ndir_norm
  have htrans : ∀ i, (1 / 2 : ℝ) ≤ |v' i 2| := by
    intro i
    have hh := hCG _ (hgJ i)
    have h2 := hh.ndir_two
    obtain ⟨hu1, -⟩ := hh.nuz_bounds
    have he4 := hh.he4
    simp only [hv']
    rw [h2, abs_of_nonneg (by linarith)]
    linarith
  have hcyl : ∀ i, tube ρ (x' i) (v' i) ⊆ safeCyl r0 e := fun i =>
    (hCG _ (hgJ i)).ntube_subset_safeCyl
  have hY'm : ∀ i, MeasurableSet (Y' i) := fun i =>
    measurableSet_nsat hfc hZ.ne' α β ρ e _ _ (hAm _)
  have hY'T : ∀ i, Y' i ⊆ tube ρ (x' i) (v' i) := fun i => nsat_subset _ _ _ _ _ _ _ _ _
  have hcount : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube ρ (x' i) (v' i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W)) := by
    intro W hW
    have hWc : Convex ℝ (W + (2 * e) • (W - W)) := hW.add ((hW.sub hW).smul _)
    set S' : Set (Fin n) :=
      {k | tube δ (x k) (v k) ⊆ zoom Z (f 0) α β ⁻¹' (W + (2 * e) • (W - W))}
    have hmap : ∀ i ∈ {i | tube ρ (x' i) (v' i) ⊆ W}, g i ∈ S' := by
      intro i hi
      exact (hCG _ (hgJ i)).zoom_tube_subset hW hi
    have hcard : (Set.ncard {i | tube ρ (x' i) (v' i) ⊆ W} : ℝ) ≤ (Set.ncard S' : ℝ) := by
      have := Set.ncard_le_ncard_of_injOn g hmap hg_inj.injOn (Set.toFinite S')
      exact_mod_cast this
    have hFW := hF _ (zoom_convex_preimage Z (f 0) α β hWc)
    rw [zoom_volume_preimage hZ] at hFW
    calc ENNReal.ofReal (Set.ncard {i | tube ρ (x' i) (v' i) ⊆ W} : ℝ)
        ≤ ENNReal.ofReal (Set.ncard S' : ℝ) := ENNReal.ofReal_le_ofReal hcard
      _ ≤ ENNReal.ofReal (δ ^ (-η) * n) *
            (ENNReal.ofReal ((Z ^ 2)⁻¹) * volume (W + (2 * e) • (W - W))) := hFW
      _ = ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hKt, div_eq_mul_inv]
  -- the density of the saturated shadings
  have hsum : ∑ i, volume (Y' i) = ∑ j ∈ J, volume (nsat f Z α β ρ e (x j) (v j) (A j)) := by
    rw [← Finset.sum_coe_sort J]
    exact Equiv.sum_comp eJ (fun j : { j // j ∈ J } =>
      volume (nsat f Z α β ρ e (x j) (v j) (A j)))
  set k := ρ * Z * (|f 0| - 2) / (18 * δ) with hk
  have hk0 : 0 ≤ k := by
    rw [hk]; apply div_nonneg _ (by positivity)
    have : 0 ≤ |f 0| - 2 := by linarith
    positivity
  have hsat : ∀ j ∈ J, ENNReal.ofReal k * volume (A j) ≤
      volume (nsat f Z α β ρ e (x j) (v j) (A j)) := fun j hj =>
    (hCG j hj).volume_nsat_ge hf (hAm j) (hAsub j)
  have hdens : ENNReal.ofReal (ρ ^ ηG * (m : ℝ) * ρ ^ 2) ≤ ∑ i, volume (Y' i) := by
    rw [hsum]
    calc ENNReal.ofReal (ρ ^ ηG * (m : ℝ) * ρ ^ 2)
        ≤ ENNReal.ofReal k * ENNReal.ofReal (200 * ρ ^ ηG * (m : ℝ) * δ ^ 2) := by
          rw [← ENNReal.ofReal_mul hk0]
          apply ENNReal.ofReal_le_ofReal
          have hρη : 0 < ρ ^ ηG := Real.rpow_pos_of_pos hρ0 _
          have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
          have hkey : ρ ^ 2 ≤ k * (200 * δ ^ 2) := by
            have h1 : k * (200 * δ ^ 2) = ρ * (100 / 9 * Z * (|f 0| - 2) * δ) := by
              rw [hk]; field_simp; ring
            rw [h1, sq]
            apply mul_le_mul_of_nonneg_left _ hρ0.le
            rw [h0.hρ]
            have hZδ : 0 < Z * δ := mul_pos hZ hδ
            nlinarith
          calc ρ ^ ηG * (m : ℝ) * ρ ^ 2 ≤ ρ ^ ηG * m * (k * (200 * δ ^ 2)) :=
                mul_le_mul_of_nonneg_left hkey (by positivity)
            _ = k * (200 * ρ ^ ηG * (m : ℝ) * δ ^ 2) := by ring
      _ ≤ ENNReal.ofReal k * ∑ j ∈ J, volume (A j) := by gcongr
      _ = ∑ j ∈ J, ENNReal.ofReal k * volume (A j) := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ J, volume (nsat f Z α β ρ e (x j) (v j) (A j)) := Finset.sum_le_sum hsat
  -- apply the black box
  have hkey := hGB ρ r0 e hρ0 hρd hρr h0.he16 h0.he4 m x' v' Y' Kt hm hunit htrans hcyl hY'm hY'T
    hcount hdens (fun w => f w - f 0) (slopeN_centred hf) (by simp)
  -- the projection of the saturations lies over `G`
  have hproj : proj (fun w => f w - f 0) (⋃ i, Y' i) ⊆ unzoom f Z α β ⁻¹' G := by
    rintro _ ⟨p', hp', rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp'
    obtain ⟨p, hp, hpe⟩ := nsat_proj hZ.ne' hi
    show unzoom f Z α β (pmap (fun w => f w - f 0) p') ∈ G
    rw [← hpe]
    exact hp.1.2
  calc ENNReal.ofReal (ρ ^ εG * (m : ℝ))
      ≤ ENNReal.ofReal (CG' * Kt) * volume (proj (fun w => f w - f 0) (⋃ i, Y' i)) := hkey
    _ ≤ ENNReal.ofReal (CG' * Kt) * volume (unzoom f Z α β ⁻¹' G) := by
        gcongr
    _ = ENNReal.ofReal (CG' * Kt) * (ENNReal.ofReal Z * volume G) := by
        rw [volume_unzoom_preimage hfc hZ α β hGm]

end WangZahlLot.Obl.wz_intermediate_twist_normalization
