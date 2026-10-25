import Submission.Obl.k4_general_parent_projected_layers.Worlds
import Submission.Obl.k4_general_parent_projected_layers.Assembly

/-!
# The single-depth step from prepared worlds

`WorldPreparation` is what the support and pruning geometry has to supply at one
depth: for every loss exponent of Scalar's input, every dense current law has a
submeasure and finitely many disjoint ready worlds whose crops carry half of its mass.
`singleLayer_of_worlds` turns it, with Scalar, into the single-depth step
`SingleLayer`; `ordinaryPreparation_of_worlds` into ordinary preparation.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_horizontal_supercritical_three_projections (chartLaw)

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- Prepared worlds at depth `s`, mesh `χ = N^(-m)` and Scalar parameters `M, C`: for
Scalar's loss exponent `η₁` and every mass loss `θ`, dense current laws have a
submeasure and finitely many disjoint ready worlds whose priors carry their mass up to
`N^(-θ)`. -/
def WorldPreparation (p : Parameters) (a : PreparedModel α) (s m M C : ℝ) : Prop :=
  ∀ η₁ : ℝ, 0 < η₁ → ∀ θ : ℝ, 0 < θ → ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop,
    ∀ ζ : Measure (α × ℝ), ζ ≤ a.rho k → ENNReal.ofReal (p.N k ^ (-η)) ≤ ζ univ →
      ∃ (ζ₀ : Measure (α × ℝ)) (Q : Finset (Fin 4 → ℤ)) (W : (Fin 4 → ℤ) → ScalarWorld α),
        ζ₀ ≤ ζ ∧
        (∀ u ∈ Q, (W u).Ready (p.N k) η₁ p.d s M C (p.N k ^ (-m)) (p.N k ^ (-p.ell * s))
          (2 * p.K k) (a.b k) (a.P k) (a.nu k) (a.pi k) ζ₀) ∧
        (∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → Disjoint (W u).crop (W u').crop) ∧
        (ζ univ).toReal * p.N k ^ (-θ) ≤ ∑ u ∈ Q, (a.nu k (W u).crop).toReal

/-- Prepared worlds at every depth of `[a, 2a]` and every mesh exponent above `L a`, with
Scalar mesh exponent at most `L a`. -/
def WorldsPrepared (p : Parameters) (a : PreparedModel α) : Prop :=
  ∃ L : ℝ, 2 < L ∧ ∀ a₀ : ℝ, 0 < a₀ → 2 * a₀ < p.U → ∀ s : ℝ, a₀ ≤ s → s ≤ 2 * a₀ →
    ∀ m : ℝ, L * a₀ < m → ∃ M C : ℝ, s < M ∧ M ≤ L * a₀ ∧ 0 < C ∧
      a.WorldPreparation p s m M C

/-- The mass of the crops is controlled by their priors. -/
theorem crops_mass_le (p : Parameters) (a : PreparedModel α) (hcommon : a.Common p) (k : ℕ)
    {ζ : Measure (α × ℝ)} (hζ : ζ ≤ a.rho k) {ι : Type*} (Q : Finset ι) (crop : ι → Set α) :
    ζ (⋃ u ∈ Q, crop u ×ˢ (univ : Set ℝ)) ≤ ENNReal.ofReal (p.K k) * ∑ u ∈ Q, a.nu k (crop u) := by
  obtain ⟨_, _, _, hdom, hρ, hsupp, -⟩ := hcommon k
  rw [Finset.mul_sum]
  refine (measure_biUnion_finset_le Q _).trans (Finset.sum_le_sum fun u _ => ?_)
  have h1 : ζ (crop u ×ˢ (univ : Set ℝ)) ≤ a.mu k (crop u ×ˢ Icc (0 : ℝ) 1) := by
    calc ζ (crop u ×ˢ (univ : Set ℝ)) ≤ a.mu k (crop u ×ˢ (univ : Set ℝ)) := (hζ.trans hρ) _
      _ ≤ a.mu k (crop u ×ˢ Icc (0 : ℝ) 1 ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := by
          apply measure_mono
          rintro ⟨l, t⟩ ⟨hl, -⟩
          by_cases ht : t ∈ Icc (0 : ℝ) 1
          · exact Or.inl ⟨hl, ht⟩
          · exact Or.inr fun h => ht h.2
      _ ≤ a.mu k (crop u ×ˢ Icc (0 : ℝ) 1) + a.mu k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
          measure_union_le _ _
      _ = a.mu k (crop u ×ˢ Icc (0 : ℝ) 1) := by rw [hsupp, add_zero]
  refine h1.trans ((hdom _).trans_eq ?_)
  rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
  simp

/-- Prepared worlds and Scalar give the single-depth step. -/
theorem singleLayer_of_worlds (hScalar : Scalar) (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcommon : a.Common p) {s La m M C : ℝ} (hs : 0 < s)
    (hsM : s < M) (hMLa : M ≤ La) (hC : 0 < C) (hw : a.WorldPreparation p s m M C) :
    a.SingleLayer p s La m := by
  classical
  intro ε hε
  obtain ⟨hN2, hNt, ⟨hK1, hKsub⟩, hd, hd1, -, -, hℓ, -⟩ := hp
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨η₁, hη₁, N₀, hN₀, H⟩ := layer_of_worlds hScalar hd hd1 hs hsM hC hε4 hε4
  obtain ⟨η₂, hη₂, Hw⟩ := hw η₁ hη₁ (ε / 4) hε4
  set B : ℝ := ((widthIndices (M + ε / 4) (ε / 4) (ε / 4)).card : ℝ) with hBdef
  have hB1 : 1 ≤ B := by
    have hne := widthIndices_nonempty (A := M + ε / 4) (B := ε / 4) (by linarith)
      hε4.le hε4
    have := hne.card_pos
    rw [hBdef]
    exact_mod_cast this
  have hpowt : ∀ c : ℝ, 0 < c → Tendsto (fun k => p.N k ^ c) atTop atTop :=
    fun c hc => (tendsto_rpow_atTop hc).comp hNt
  refine ⟨min η₂ (ε / 4), lt_min hη₂ hε4, ?_⟩
  filter_upwards [Hw, hNt.eventually_ge_atTop N₀, hKsub (ε / 4) hε4,
    (hpowt (ε / 4) hε4).eventually_ge_atTop B,
    (hpowt (ε / 2) (by positivity)).eventually_ge_atTop 3] with k Hk hNk hKk hNB hN3
  intro ζ hζ hmass
  have := (hcommon k).2.1
  have := (hcommon k).2.2.1
  have hN1 : 1 ≤ p.N k := le_trans (by norm_num) (hN2 k)
  have hN0 : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN1
  have hK0 : 0 ≤ p.K k := le_trans zero_le_one (hK1 k)
  have hmass₂ : ENNReal.ofReal (p.N k ^ (-η₂)) ≤ ζ univ := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    exact Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_left _ _))
  obtain ⟨ζ₀, Q, W, hζ₀, hready, hdisj, hprior⟩ := Hk ζ hζ hmass₂
  have hg1 : p.N k ^ (-p.ell * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  obtain ⟨L, hL, hLmass⟩ := H (p.N k) hNk α (a.nu k) (a.pi k) ζ₀ (a.rho k) (a.b k) (a.P k)
    (Fin 4 → ℤ) Q W (p.N k ^ (-m)) (p.N k ^ (-p.ell * s)) (2 * p.K k) p.ell La
    (hζ₀.trans hζ) (Real.rpow_nonneg hN0.le _) rfl hg1 (by linarith) hMLa hready hdisj
  have hcov : MeasurableSet L.covered := ProjLayer.measurableSet_covered hL.2.2.2.1
  refine ⟨L, ζ₀.restrict L.covered, Measure.restrict_le_self.trans hζ₀, ?_,
    ae_restrict_mem hcov, ?_⟩
  · -- the retained mass
    rw [Measure.restrict_apply_univ]
    have hsum : (∑ u ∈ Q, ENNReal.ofReal ((a.nu k (W u).crop).toReal * p.N k ^ (-(ε / 4)))) =
        ENNReal.ofReal (p.N k ^ (-(ε / 4)) * ∑ u ∈ Q, (a.nu k (W u).crop).toReal) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun u _ => by positivity)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul_comm]
    set X := ζ₀ L.covered
    set Sr := ∑ u ∈ Q, (a.nu k (W u).crop).toReal
    have hSr : 0 ≤ Sr := Finset.sum_nonneg fun u _ => ENNReal.toReal_nonneg
    have hζfin : ζ univ ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (hζ univ)
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (a.rho_univ_le p hcommon k)
    have hmassr : p.N k ^ (-(min η₂ (ε / 4))) ≤ (ζ univ).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hζfin).mp hmass
    -- the numerical comparison
    have hreal : p.N k ^ (-ε) * B ≤ p.N k ^ (-(ε / 4)) * Sr := by
      have hexp : -ε + ε / 4 ≤ -(ε / 4) + (-(min η₂ (ε / 4)) + -(ε / 4)) := by
        have := min_le_right η₂ (ε / 4)
        linarith
      calc p.N k ^ (-ε) * B ≤ p.N k ^ (-ε) * p.N k ^ (ε / 4) :=
            mul_le_mul_of_nonneg_left hNB (Real.rpow_nonneg hN0.le _)
        _ = p.N k ^ (-ε + ε / 4) := (Real.rpow_add hN0 _ _).symm
        _ ≤ p.N k ^ (-(ε / 4) + (-(min η₂ (ε / 4)) + -(ε / 4))) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hexp
        _ = p.N k ^ (-(ε / 4)) * (p.N k ^ (-(min η₂ (ε / 4))) * p.N k ^ (-(ε / 4))) := by
            rw [Real.rpow_add hN0, Real.rpow_add hN0]
        _ ≤ p.N k ^ (-(ε / 4)) * ((ζ univ).toReal * p.N k ^ (-(ε / 4))) := by
            gcongr
        _ ≤ p.N k ^ (-(ε / 4)) * Sr := by
            gcongr
    have hB0 : (ENNReal.ofReal B) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hB1)).ne'
    have hfinal : ENNReal.ofReal (p.N k ^ (-ε)) * ENNReal.ofReal B ≤ X * ENNReal.ofReal B := by
      calc ENNReal.ofReal (p.N k ^ (-ε)) * ENNReal.ofReal B
          = ENNReal.ofReal (p.N k ^ (-ε) * B) :=
            (ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _)).symm
        _ ≤ ENNReal.ofReal (p.N k ^ (-(ε / 4)) * Sr) := ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal B * X := by
            have hBc : ENNReal.ofReal B =
                ((widthIndices (M + ε / 4) (ε / 4) (ε / 4)).card : ENNReal) := by
              rw [hBdef, ENNReal.ofReal_natCast]
            rw [← hsum, hBc]
            exact hLmass
        _ = X * ENNReal.ofReal B := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_left hB0 ENNReal.ofReal_ne_top).mp hfinal
  · -- the loss: `(2K + N^(ε/4)) N^(ε/4) ≤ 3 N^(ε/2) ≤ N^ε`
    have hpow4 : 1 ≤ p.N k ^ (ε / 4) := Real.one_le_rpow hN1 hε4.le
    have hH0 : 0 < (2 * p.K k + p.N k ^ (ε / 4)) * p.N k ^ (ε / 4) := by positivity
    refine hL.mono hN0 hH0 ?_ (Real.rpow_nonneg hN0.le _)
    have h2 : p.N k ^ (ε / 4) * p.N k ^ (ε / 4) = p.N k ^ (ε / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have h3 : p.N k ^ (ε / 2) * p.N k ^ (ε / 2) = p.N k ^ ε := by
      rw [← Real.rpow_add hN0]; ring_nf
    calc (2 * p.K k + p.N k ^ (ε / 4)) * p.N k ^ (ε / 4)
        ≤ (3 * p.N k ^ (ε / 4)) * p.N k ^ (ε / 4) := by
          gcongr
          linarith
      _ = 3 * p.N k ^ (ε / 2) := by rw [mul_assoc, h2]
      _ ≤ p.N k ^ (ε / 2) * p.N k ^ (ε / 2) := by
          gcongr
      _ = p.N k ^ ε := h3

/-- Prepared worlds at every depth give ordinary preparation. -/
theorem ordinaryPreparation_of_worlds (hScalar : Scalar) (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcommon : a.Common p) (hw : a.WorldsPrepared p) :
    a.OrdinaryPreparation p := by
  obtain ⟨L, hL, H⟩ := hw
  refine ⟨L, hL, fun a₀ ha₀ hU s hs₁ hs₂ m hm => ?_⟩
  obtain ⟨M, C, hsM, hML, hC, hwp⟩ := H a₀ ha₀ hU s hs₁ hs₂ m hm
  exact singleLayer_of_worlds hScalar p hp a hcommon (by linarith) hsM hML hC hwp

end PreparedModel

/-- The geometric principle left for o253: every valid prepared model has prepared
worlds at every depth. It does not involve Scalar. -/
def WorldsPrinciple : Prop :=
  ∀ (p : Parameters), p.Valid → ∀ (α : Type) [MeasurableSpace α] (a : PreparedModel α),
    a.Valid p → a.WorldsPrepared p

theorem scalarPreparation_of_worlds (h : WorldsPrinciple) : ScalarPreparation := by
  intro hScalar p hp α _ a ha
  exact PreparedModel.ordinaryPreparation_of_worlds hScalar p hp a ha.1 (h p hp α a ha)


end

end Submission.Obl.k4_general_parent_projected_layers
