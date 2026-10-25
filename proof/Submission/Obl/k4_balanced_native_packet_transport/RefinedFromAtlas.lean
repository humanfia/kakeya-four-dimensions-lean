import Submission.Obl.k4_balanced_native_packet_transport.Refined
import Submission.Obl.k4_balanced_native_packet_transport.TrackingNative
import Submission.Obl.k4_balanced_native_packet_transport.Pullback
import Submission.Obl.k4_balanced_native_packet_transport.FullnessMass

/-!
The tangentially full pulled-back saturated packets of one tracked sample form
a valid refinement of its native charts. The non-full packets pin the original
velocity and are charged to the terminal angular density.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport
namespace RefinedFromAtlas

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedPacketSystems

noncomputable section
set_option linter.unusedVariables false

/-- An o184 chart is a frozen chart, with its final clause weakened. -/
theorem chart_of_Chart {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ} {Ev : Set Inc}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Traj} {F : Set Inc} {ex ex' : Prop}
    (h : Submission.Obl.k4_remainder_pure_profile_normalization.Chart Nk M D κ T j r Bv Ev
      c u Q R A F ex) (himp : ex → ex') :
    chart Nk M D κ T j r Bv Ev c u Q R A F ex' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hex⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, himp hex⟩

/-- An incidence set inside a closed time window loses no product mass when its right
endpoint is removed. -/
theorem prod_le_Ico (μ : Measure Traj) {F : Set Inc} {t₀ t₁ : ℝ}
    (hF : ∀ z ∈ F, z.2 ∈ Icc t₀ t₁) :
    (μ.prod volume) F ≤ (μ.prod volume) (F ∩ (univ ×ˢ Ico t₀ t₁)) := by
  have hsub : F ⊆ (F ∩ (univ ×ˢ Ico t₀ t₁)) ∪ (univ ×ˢ {t₁}) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hF z hz
    rcases lt_or_eq_of_le h2 with h2 | h2
    · exact Or.inl ⟨hz, mem_univ _, h1, h2⟩
    · exact Or.inr ⟨mem_univ _, h2⟩
  have hnull : (μ.prod volume) (univ ×ˢ ({t₁} : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
  calc (μ.prod volume) F ≤ (μ.prod volume) ((F ∩ (univ ×ˢ Ico t₀ t₁)) ∪ (univ ×ˢ {t₁})) :=
        measure_mono hsub
    _ ≤ (μ.prod volume) (F ∩ (univ ×ˢ Ico t₀ t₁)) + (μ.prod volume) (univ ×ˢ {t₁}) :=
        measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]

/-- Half-open dyadic blocks of one generation are disjoint. -/
theorem block_eq {T j j' : ℕ} {t : ℝ}
    (h : t ∈ Ico ((j : ℝ) / 2 ^ T) ((j : ℝ) / 2 ^ T + 1 / 2 ^ T))
    (h' : t ∈ Ico ((j' : ℝ) / 2 ^ T) ((j' : ℝ) / 2 ^ T + 1 / 2 ^ T)) : j = j' := by
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have a1 : (j : ℝ) < j' + 1 := by
    have := h1.trans_lt h2'
    rw [← add_div, div_lt_div_iff_of_pos_right hT] at this
    exact this
  have a2 : (j' : ℝ) < j + 1 := by
    have := h1'.trans_lt h2
    rw [← add_div, div_lt_div_iff_of_pos_right hT] at this
    exact this
  have b1 : j < j' + 1 := by exact_mod_cast a1
  have b2 : j' < j + 1 := by exact_mod_cast a2
  omega

/-- Velocity pinning in the rotation-scaling frame, with the frame bounds as inputs. -/
theorem pin_bound {Q' : Matrix (Fin 2) (Fin 2) ℝ} {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1)
    {g : ℝ} (hg : 0 ≤ g) (hQ : (!![e 0, -g * e 1; e 1, g * e 0] * Q').det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) {t₀ q κ A₁ A₂ : ℝ} (hq : 0 < q) (l : Traj)
    (hframe : ∀ t ∈ Set.Icc t₀ (t₀ + q),
      ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q')⁻¹ (y l t - c - t • u)‖ ≤ κ)
    (h1 : ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose e‖ ≤ A₁)
    (h2 : (∑ i, ∑ j, |Q' i j|) ≤ A₂) :
    ‖v l - u‖ ≤ 2 * κ * (A₁ + g * A₂) / q := by
  have h01 : ‖(WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    have h := FullnessMass.norm_sq_fin2 (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have h0 := norm_nonneg (WithLp.toLp 2 ![(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2))
    nlinarith
  have ha' : ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose
      (WithLp.toLp 2 ![-e 1, e 0])‖ ≤ g * A₂ := by
    rw [FullnessMass.norm_frame_transpose_perp he hg Q']
    have := FullnessMass.norm_toEuclideanLin_transpose_le Q' (WithLp.toLp 2 ![0, 1])
    rw [h01, mul_one] at this
    exact mul_le_mul_of_nonneg_left (this.trans h2) hg
  exact FullnessMass.norm_v_sub_le hQ c u hq l hframe he (FullnessMass.norm_perp he)
    (FullnessMass.inner_perp e) h1 ha'

/-- Velocity pinning of a trajectory in a non-full chart on the dyadic block `j` of
generation `T`: the tangential frame norm is below `2⁻ᵀ / N ^ loss` and the child frame
is thin. -/
theorem pin_chart {Q Q' : Matrix (Fin 2) (Fin 2) ℝ} {e : EuclideanSpace ℝ (Fin 2)}
    (he : ‖e‖ = 1) {g : ℝ} (hg : 0 ≤ g) (hQeq : Q = !![e 0, -g * e 1; e 1, g * e 0] * Q')
    (hQ : Q.det ≠ 0) (c u : EuclideanSpace ℝ (Fin 2)) {T j : ℕ} {κ loss N : ℝ} (hN : 0 < N)
    (l : Traj)
    (hframe : ∀ t ∈ Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ)
    (h1 : ‖Matrix.toEuclideanLin Q.transpose e‖ ≤ 1 / 2 ^ T / N ^ loss)
    (h2 : (∑ i, ∑ j, |Q' i j|) ≤ κ / 2 ^ T) :
    ‖v l - u‖ ≤ 2 * κ * (1 / N ^ loss + g * κ) := by
  subst hQeq
  have hq : (0 : ℝ) < 1 / 2 ^ T := by positivity
  have hframe' : ∀ t ∈ Icc ((j : ℝ) / 2 ^ T) ((j : ℝ) / 2 ^ T + 1 / 2 ^ T),
      ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q')⁻¹ (y l t - c - t • u)‖ ≤
        κ := by
    intro t ht
    rw [← add_div] at ht
    exact hframe t ht
  have hb := pin_bound he hg hQ c u hq l hframe' h1 h2
  have hNl : 0 < N ^ loss := Real.rpow_pos_of_pos hN _
  have hP : (0 : ℝ) < 2 ^ T := by positivity
  have e1 : 2 * κ * (1 / 2 ^ T / N ^ loss + g * (κ / 2 ^ T)) / (1 / 2 ^ T) =
      2 * κ * (1 / N ^ loss + g * κ) := by
    field_simp
  rw [e1] at hb
  exact hb

/-- A set is covered by its part off `Bad` and `Bad` itself. -/
theorem measure_le_inter_compl_add {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (U Bad : Set α) : μ U ≤ μ (U ∩ Badᶜ) + μ Bad := by
  refine (measure_mono fun z hz => ?_).trans (measure_union_le (U ∩ Badᶜ) Bad)
  by_cases hb : z ∈ Bad
  · exact Or.inr hb
  · exact Or.inl ⟨hz, hb⟩

/-- The frozen problem as a problem of the cap package. -/
def uweProblem (N K : ℕ → ℝ) (d : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Traj)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal) : UWE.Problem :=
  ⟨N, K, 1, d, W, ω, ν, E, P, B, f, g, G⟩

theorem refined_of_atlas
    {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    (hprob : prob N K 1 d S η W ω ν E P B f g G)
    (q : Certificate (TrackingNative.toData N K d S η W ω ν E P B f g G)) (n : ℕ)
    {M D : ℕ} {a₀ w χ₀ ds s m S' U ℓ : ℝ}
    (σ : NativeSample (W (q.sequence.index n)))
    (hσ : σ.Holds false (N (q.sequence.index n)) (K (q.sequence.index n))
      (ω (q.sequence.index n)) (ν (q.sequence.index n)) (E (q.sequence.index n))
      (P (q.sequence.index n)) (B (q.sequence.index n)) M D a₀ w ℓ 1 χ₀ ds s m S' U)
    (hsub : Tracking.SubOf (q.sequence.atlas n)
      (TrackingNative.nativeAtlas (TrackingNative.toData N K d S η W ω ν E P B f g G)
        (q.sequence.index n) σ (N (q.sequence.index n) ^ ℓ)))
    {M₁ D₁ : ℕ} {r ε h err : ℝ}
    (a : CPF.Atlas (normalizedData q) n) (ha : a.SaturatedAt M₁ D₁ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hκ1 : 1 ≤ a.κ) (hκε : a.κ ≤ N (q.sequence.index n) ^ ε)
    (hT : (2 : ℝ) ^ a.T ≤ N (q.sequence.index n) ^ h)
    (hcov : ENNReal.ofReal (N (q.sequence.index n) ^ (-ε)) ≤
      CPF.OriginalPacketCoverage.originalCoveredMass q n a)
    (hband : ∀ c, N (q.sequence.index n) ^ (-ds * r - (3 * err + ε)) ≤
      originalMass q n a c /
        (N (q.sequence.index n) ^ (-f 0) * |(composedFrame q n a c).det|))
    (hPκ : (q.sequence.atlas n).κ ≤ N (q.sequence.index n) ^ ε)
    {loss χ ξ u τ c₀ : ℝ} {Mout Dout : ℕ}
    (hMout : q.M + M₁ + 1 ≤ Mout) (hDout : max q.D D₁ ≤ Dout)
    (hε : 0 < ε) (hεloss : 2 * ε ≤ loss) (hloss : 0 < loss) (hh : 0 ≤ h)
    (hξ : ds * r + 3 * err + ε ≤ ξ)
    (hu : 0 < u) (huη : u ≤ η)
    (hbad : ∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
        (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
          (UWE.angularDensityBad (uweProblem N K d W ω ν E P B f g G) S
              (q.sequence.index n) γ u τ ∪
            UWE.pureDensityBad (uweProblem N K d W ω ν E P B f g G)
              (q.sequence.index n) γ 1 τ) ≤
      ENNReal.ofReal (N (q.sequence.index n) ^ (-c₀)))
    (hnum : ENNReal.ofReal (N (q.sequence.index n) ^ (-loss)) +
        ENNReal.ofReal (N (q.sequence.index n) ^ (-χ)) +
        ENNReal.ofReal (N (q.sequence.index n) ^ (-a₀)) +
        ENNReal.ofReal (N (q.sequence.index n) ^ (-S * u + 2 * τ) *
          N (q.sequence.index n) ^ (2 * ε) *
          (2 * (2 * N (q.sequence.index n) ^ (2 * ε) *
              (N (q.sequence.index n) ^ (-loss) +
                N (q.sequence.index n) ^ (-w) * N (q.sequence.index n) ^ ε)) /
            δ (N (q.sequence.index n)) u + 2) ^ 2) +
        ENNReal.ofReal (N (q.sequence.index n) ^ (-c₀)) ≤
      ENNReal.ofReal (N (q.sequence.index n) ^ (-ε))) :
    ∃ ρ : Refined.Family (W (q.sequence.index n)) σ.C,
      ρ.Valid σ (N (q.sequence.index n)) (ν (q.sequence.index n)) (E (q.sequence.index n))
        (P (q.sequence.index n)) (B (q.sequence.index n)) Mout Dout loss h (f 0) ξ ∧
      ENNReal.ofReal (N (q.sequence.index n) ^ (-loss)) +
          ENNReal.ofReal (N (q.sequence.index n) ^ (-χ)) +
          ENNReal.ofReal (N (q.sequence.index n) ^ (-a₀)) ≤
        ∑ i, ENNReal.ofReal (ω (q.sequence.index n) (σ.γ (ρ.parent i))) *
          ((ν (q.sequence.index n) (σ.γ (ρ.parent i))).prod volume) (ρ.H i) := by
  classical
  obtain ⟨-, hTeq, ι, hι⟩ := hsub
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hσT, htan, ⟨gg, hg0, hgw, hQform⟩, -⟩ := hσ
  have hp := TrackingNative.toData_valid hprob
  have hTP : (q.sequence.atlas n).T = 0 := hTeq.trans hσT
  have hγ : ∀ b, (q.sequence.atlas n).γ b = σ.γ (ι b) := fun b => Fin.ext (hι b).1
  have hR : ∀ b, (q.sequence.atlas n).R b =
      (TrackingNative.toData N K d S η W ω ν E P B f g G).P (q.sequence.index n)
        ((q.sequence.atlas n).γ b) := by
    intro b
    rw [(hι b).2.2.2.2.2.1, hγ b]
    rfl
  have hpw : ∀ c, Pullback.pullWorld q n a c = σ.γ (ι (a.γ c)) := fun c => hγ (a.γ c)
  have hνprob : ∀ γ, IsProbabilityMeasure (ν (q.sequence.index n) γ) := by
    obtain ⟨M', D', hreg⟩ := hprob.2.2.2.2.2.2.2.2.1
    exact fun γ => ((hreg (q.sequence.index n)).2.2.2.1 γ).1
  have hAeq : ∀ b, (q.sequence.atlas n).A b = σ.A (ι b) := fun b => (hι b).2.2.2.2.2.2.1
  have hFeq : ∀ b, (q.sequence.atlas n).F b = σ.F (ι b) := fun b => (hι b).2.2.2.2.2.2.2
  have hQeq : ∀ b, (q.sequence.atlas n).Q b = σ.Q (ι b) := fun b => (hι b).2.2.2.2.1
  -- numerics
  have hN2 : 2 ≤ N (q.sequence.index n) := hprob.1 _
  have hN0 : 0 < N (q.sequence.index n) := by linarith
  have hN1 : 1 ≤ N (q.sequence.index n) := by linarith
  have hκ2 : (q.sequence.atlas n).κ * a.κ ≤ N (q.sequence.index n) ^ (2 * ε) := by
    calc (q.sequence.atlas n).κ * a.κ
        ≤ N (q.sequence.index n) ^ ε * N (q.sequence.index n) ^ ε :=
          mul_le_mul hPκ hκε (by linarith) (by positivity)
      _ = N (q.sequence.index n) ^ (2 * ε) := by
          rw [← Real.rpow_add hN0]; ring_nf
  have hκprod : (q.sequence.atlas n).κ * a.κ ≤ N (q.sequence.index n) ^ loss :=
    hκ2.trans (Real.rpow_le_rpow_of_exponent_le hN1 hεloss)
  obtain ⟨hcount, hpsep, hpcard, hpmeas, hpchart⟩ :=
    Pullback.pullback_system q n a hp rfl hTP hR ha hr1 hκ1 hκprod hMout hDout
  -- the full charts
  let full : Fin a.C → Prop := fun c => 1 / (2 : ℝ) ^ a.T / N (q.sequence.index n) ^ loss ≤
    ‖Matrix.toEuclideanLin (composedFrame q n a c).transpose (Refined.tangentAxis σ (ι (a.γ c)))‖
  let Sf : Finset (Fin a.C) := Finset.univ.filter full
  let emb : Fin Sf.card → Fin a.C := fun i => (Sf.equivFin.symm i).1
  have hemb_inj : Function.Injective emb := by
    intro i i' h
    exact Sf.equivFin.symm.injective (Subtype.ext h)
  have hemb_full : ∀ i, full (emb i) := fun i => (Finset.mem_filter.mp (Sf.equivFin.symm i).2).2
  let ρ : Refined.Family (W (q.sequence.index n)) σ.C :=
    { T := a.T
      C := Sf.card
      parent := fun i => ι (a.γ (emb i))
      j := fun i => a.j (emb i)
      c := fun i => Pullback.pullCenter q n a (emb i)
      u := fun i => Pullback.pullVelocity q n a (emb i)
      Q := fun i => composedFrame q n a (emb i)
      A := fun i => originalAssignment q n a (emb i)
      F := fun i => CPF.OriginalPacketCoverage.originalEvent q n a (emb i)
      lst := fun γ o => Finset.univ.filter (fun i => emb i ∈ Pullback.pullList q n a γ o) }
  have hmem_lst : ∀ γ o i, i ∈ ρ.lst γ o ↔ emb i ∈ Pullback.pullList q n a γ o := by
    intro γ o i
    show i ∈ Finset.univ.filter (fun i => emb i ∈ Pullback.pullList q n a γ o) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨ρ, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- A_sub
    intro i l hl
    have h1 : l ∈ (q.sequence.atlas n).A (a.γ (emb i)) := hl.1
    rw [hAeq (a.γ (emb i))] at h1
    exact h1
  · -- F_sub
    intro i z hz
    have h1 := CPF.OriginalPacketCoverage.originalEvent_subset_parent q ha.1 (emb i) hz
    rw [hFeq (a.γ (emb i))] at h1
    exact h1
  · -- charts
    intro i
    have hch := hpchart (emb i)
    rw [hpw (emb i)] at hch
    exact chart_of_Chart hch (fun hex z hz => (hmem_lst _ _ i).mpr (hex z hz))
  · -- sep
    intro i i' hii' hγeq hjeq
    have hne : emb i ≠ emb i' := fun h => hii' (hemb_inj h)
    exact hpsep _ _ hne (by rw [hpw, hpw]; exact hγeq) hjeq
  · -- lst_card
    intro γ o
    have h1 : (ρ.lst γ o).card ≤ (Pullback.pullList q n a γ o).card := by
      apply Finset.card_le_card_of_injOn emb
      · intro i hi
        exact (hmem_lst γ o i).mp hi
      · intro i _ i' _ h
        exact hemb_inj h
    calc ((ρ.lst γ o).card : ℝ) ≤ (Pullback.pullList q n a γ o).card := by exact_mod_cast h1
      _ ≤ (q.sequence.atlas n).κ * a.κ := hpcard γ o
      _ ≤ _ := hκprod
  · -- lst_meas
    intro γ i
    have : {o | i ∈ ρ.lst γ o} = {o | emb i ∈ Pullback.pullList q n a γ o} := by
      ext o
      exact hmem_lst γ o i
    rw [this]
    exact hpmeas γ (emb i)
  · -- count
    show ((Sf.card : ℕ) : ℝ) ≤ N (q.sequence.index n) ^ Mout
    have : Sf.card ≤ a.C := (Finset.card_le_univ Sf).trans (by simp)
    calc ((Sf.card : ℕ) : ℝ) ≤ a.C := by exact_mod_cast this
      _ ≤ _ := hcount
  · -- time
    show (2 : ℝ) ^ a.T ≤ N (q.sequence.index n) ^ (h + loss)
    exact hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · -- prior_lower
    intro i
    show ENNReal.ofReal (N (q.sequence.index n) ^ (-f 0 - ξ) *
        |Matrix.det (composedFrame q n a (emb i))|) ≤
      ν (q.sequence.index n) (σ.γ (ι (a.γ (emb i)))) (originalAssignment q n a (emb i))
    have hdet : 0 < |(composedFrame q n a (emb i)).det| :=
      abs_pos.mpr (Pullback.pull_det q n a ha.1 (emb i))
    have hf0 : 0 < N (q.sequence.index n) ^ (-f 0) := Real.rpow_pos_of_pos hN0 _
    have hb := hband (emb i)
    rw [le_div_iff₀ (mul_pos hf0 hdet)] at hb
    have hexp : N (q.sequence.index n) ^ (-f 0 - ξ) ≤
        N (q.sequence.index n) ^ (-ds * r - (3 * err + ε)) * N (q.sequence.index n) ^ (-f 0) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have := hνprob (σ.γ (ι (a.γ (emb i))))
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    calc N (q.sequence.index n) ^ (-f 0 - ξ) * |(composedFrame q n a (emb i)).det|
        ≤ N (q.sequence.index n) ^ (-ds * r - (3 * err + ε)) * N (q.sequence.index n) ^ (-f 0) *
            |(composedFrame q n a (emb i)).det| := mul_le_mul_of_nonneg_right hexp hdet.le
      _ = N (q.sequence.index n) ^ (-ds * r - (3 * err + ε)) *
            (N (q.sequence.index n) ^ (-f 0) * |(composedFrame q n a (emb i)).det|) := by ring
      _ ≤ originalMass q n a (emb i) := hb
      _ = _ := by
        unfold originalMass
        rw [hγ (a.γ (emb i))]
        rfl
  · -- full
    intro i
    exact hemb_full i
  · -- coverage
    let pw : Fin a.C → Fin (W (q.sequence.index n)) := fun c => σ.γ (ι (a.γ c))
    let qq : ℝ := 1 / (2 : ℝ) ^ a.T
    let t₀ : Fin a.C → ℝ := fun c => ((a.j c : ℕ) : ℝ) / (2 : ℝ) ^ a.T
    let Hc : Fin a.C → Set Inc := fun c =>
      CPF.OriginalPacketCoverage.originalEvent q n a c ∩ (univ ×ˢ Ico (t₀ c) (t₀ c + qq))
    let wF : Fin a.C → ENNReal := fun c => ENNReal.ofReal (ω (q.sequence.index n) (pw c)) *
      ((ν (q.sequence.index n) (pw c)).prod volume)
        (CPF.OriginalPacketCoverage.originalEvent q n a c)
    let wH : Fin a.C → ENNReal := fun c => ENNReal.ofReal (ω (q.sequence.index n) (pw c)) *
      ((ν (q.sequence.index n) (pw c)).prod volume) (Hc c)
    let NF : Finset (Fin a.C) := Finset.univ.filter (fun c => ¬ full c)
    have hFH : ∀ c, wF c ≤ wH c := by
      intro c
      refine mul_le_mul' le_rfl (prod_le_Ico _ ?_)
      intro z hz
      have := Pullback.pull_event_time q n a hTP ha.1 c z hz
      rw [add_div] at this
      exact this
    have hRHS : ∑ i, ENNReal.ofReal (ω (q.sequence.index n) (σ.γ (ρ.parent i))) *
        ((ν (q.sequence.index n) (σ.γ (ρ.parent i))).prod volume) (ρ.H i) = ∑ c ∈ Sf, wH c := by
      rw [← Finset.sum_coe_sort Sf wH]
      exact Equiv.sum_comp Sf.equivFin.symm (fun x => wH x.1)
    have hcov' : ENNReal.ofReal (N (q.sequence.index n) ^ (-ε)) ≤ ∑ c, wF c := by
      refine hcov.trans (le_of_eq ?_)
      unfold CPF.OriginalPacketCoverage.originalCoveredMass
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hγ (a.γ c)]
      rfl
    -- disjoint measurable half-open pieces in each world
    have hHm : ∀ c, MeasurableSet (Hc c) := fun c =>
      (CPF.OriginalPacketCoverage.measurableSet_originalEvent q ha.1 c).inter
        (MeasurableSet.univ.prod measurableSet_Ico)
    have hdisj : ∀ c c', c ≠ c' → pw c = pw c' → Disjoint (Hc c) (Hc c') := by
      intro c c' hcc hpwc
      rw [Set.disjoint_left]
      intro z hz hz'
      by_cases hj : a.j c = a.j c'
      · have hd := hpsep c c' hcc (by rw [hpw, hpw]; exact hpwc) hj
        exact Set.disjoint_left.mp hd
          (CPF.OriginalPacketCoverage.originalEvent_subset_assignment q ha.1 c hz.1).1
          (CPF.OriginalPacketCoverage.originalEvent_subset_assignment q ha.1 c' hz'.1).1
      · exact hj (Fin.ext (block_eq hz.2.2 hz'.2.2))
    -- the non-full pieces of one world
    have hUeq : ∀ γ, (⋃ c ∈ NF.filter (fun c => pw c = γ), Hc c) =
        ⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c := by
      intro γ
      ext z
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, NF, exists_prop]
    have hUE : ∀ γ, (⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c) ⊆ E (q.sequence.index n) γ := by
      intro γ z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨c, hz⟩ := hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨⟨_, hcγ⟩, hzc⟩ := hz
      have h1 := CPF.OriginalPacketCoverage.originalEvent_subset_original q ha.1 c hzc.1
      rw [hγ (a.γ c)] at h1
      rw [← hcγ]
      exact h1
    have hUmass : ∀ γ, ∑ c ∈ NF.filter (fun c => pw c = γ), wH c =
        ENNReal.ofReal (ω (q.sequence.index n) γ) *
          (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
            (⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c) := by
      intro γ
      show _ = ENNReal.ofReal (ω (q.sequence.index n) γ) *
          (((ν (q.sequence.index n) γ).prod volume).restrict (E (q.sequence.index n) γ))
            (⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c)
      rw [Measure.restrict_eq_self _ (hUE γ), ← hUeq γ, measure_biUnion_finset, Finset.mul_sum]
      · refine Finset.sum_congr rfl fun c hc => ?_
        have hcγ : pw c = γ := (Finset.mem_filter.mp hc).2
        show ENNReal.ofReal (ω _ (pw c)) * ((ν _ (pw c)).prod volume) (Hc c) = _
        rw [hcγ]
      · intro c hc c' hc' hcc
        exact hdisj c c' hcc ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc').2.symm)
      · intro c _
        exact hHm c
    -- velocity pinning of the non-full charts
    have hunit : ∀ b, ‖Refined.tangentAxis σ b‖ = 1 := by
      intro b
      have h := FullnessMass.norm_sq_fin2 (Refined.tangentAxis σ b)
      have h' : (Refined.tangentAxis σ b) 0 ^ 2 + (Refined.tangentAxis σ b) 1 ^ 2 = 1 :=
        (htan b).2
      rw [h'] at h
      have h0 := norm_nonneg (Refined.tangentAxis σ b)
      nlinarith
    have hCF : ∀ c, composedFrame q n a c =
        !![(Refined.tangentAxis σ (ι (a.γ c))) 0, -gg * (Refined.tangentAxis σ (ι (a.γ c))) 1;
          (Refined.tangentAxis σ (ι (a.γ c))) 1, gg * (Refined.tangentAxis σ (ι (a.γ c))) 0] *
          a.Q c := by
      intro c
      show (q.sequence.atlas n).Q (a.γ c) * a.Q c = _
      rw [hQeq (a.γ c), hQform (ι (a.γ c))]
      rfl
    have hκN : a.κ ≤ N (q.sequence.index n) ^ (2 * ε) :=
      hκε.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
    have hpin : ∀ c, ¬ full c → ∀ z ∈ Hc c, ‖v z.1 - Pullback.pullVelocity q n a c‖ ≤
        2 * N (q.sequence.index n) ^ (2 * ε) * (N (q.sequence.index n) ^ (-loss) +
          N (q.sequence.index n) ^ (-w) * N (q.sequence.index n) ^ ε) := by
      intro c hc z hz
      have hzA : z.1 ∈ originalAssignment q n a c :=
        (CPF.OriginalPacketCoverage.originalEvent_subset_assignment q ha.1 c hz.1).1
      have hlt : ‖Matrix.toEuclideanLin (composedFrame q n a c).transpose
          (Refined.tangentAxis σ (ι (a.γ c)))‖ <
            1 / (2 : ℝ) ^ a.T / N (q.sequence.index n) ^ loss :=
        not_le.mp hc
      obtain ⟨_, _, _, hthin, _⟩ := ha.1.2.2.1 c
      have hb := pin_chart (hunit (ι (a.γ c))) hg0.le (hCF c) (Pullback.pull_det q n a ha.1 c)
        (Pullback.pullCenter q n a c) (Pullback.pullVelocity q n a c) hN0 z.1
        (fun t ht => Pullback.pull_geometry q n a hTP ha.1 c z.1 hzA t ht) hlt.le hthin
      refine hb.trans ?_
      have hκ0 : 0 ≤ a.κ := by linarith
      have hinv : 1 / N (q.sequence.index n) ^ loss = N (q.sequence.index n) ^ (-loss) := by
        rw [Real.rpow_neg hN0.le, one_div]
      rw [hinv]
      have hgκ : gg * a.κ ≤ N (q.sequence.index n) ^ (-w) * N (q.sequence.index n) ^ ε :=
        mul_le_mul hgw hκε hκ0 (by positivity)
      have hpos : 0 ≤ N (q.sequence.index n) ^ (-loss) + gg * a.κ := by positivity
      calc 2 * a.κ * (N (q.sequence.index n) ^ (-loss) + gg * a.κ)
          ≤ 2 * N (q.sequence.index n) ^ (2 * ε) * (N (q.sequence.index n) ^ (-loss) + gg * a.κ) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    -- angular charging of the non-full charts
    have hw : ∀ (γ : Fin (W (q.sequence.index n))) (c : Fin a.C),
        ∀ z ∈ ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c,
          ‖v z.1 - Pullback.pullVelocity q n a c‖ ≤
            2 * N (q.sequence.index n) ^ (2 * ε) * (N (q.sequence.index n) ^ (-loss) +
              N (q.sequence.index n) ^ (-w) * N (q.sequence.index n) ^ ε) := by
      intro γ c z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨⟨hc, _⟩, hzc⟩ := hz
      exact hpin c hc z hzc
    have hlst' : ∀ (γ : Fin (W (q.sequence.index n))) (c : Fin a.C),
        ∀ z ∈ ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c,
          c ∈ Pullback.pullList q n a γ
            (obs (B (q.sequence.index n) γ) (δ (N (q.sequence.index n)) 1) z) := by
      intro γ c z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨⟨_, hcγ⟩, hzc⟩ := hz
      refine (Pullback.mem_pullList q n a γ _ c).mpr ⟨?_, z, hzc.1, rfl⟩
      rw [hpw c]
      exact hcγ
    have hang : ∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
        (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
          ((⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c) ∩
            (UWE.angularDensityBad (uweProblem N K d W ω ν E P B f g G) S
                (q.sequence.index n) γ u τ ∪
              UWE.pureDensityBad (uweProblem N K d W ω ν E P B f g G)
                (q.sequence.index n) γ 1 τ)ᶜ) ≤
      ENNReal.ofReal (N (q.sequence.index n) ^ (-S * u + 2 * τ) *
          N (q.sequence.index n) ^ (2 * ε) *
          (2 * (2 * N (q.sequence.index n) ^ (2 * ε) *
              (N (q.sequence.index n) ^ (-loss) +
                N (q.sequence.index n) ^ (-w) * N (q.sequence.index n) ^ ε)) /
            δ (N (q.sequence.index n)) u + 2) ^ 2) :=
      FullnessMass.weighted_angular_charge_le (p := uweProblem N K d W ω ν E P B f g G)
        (S := S) (η := η) hprob rfl (q.sequence.index n) hu huη τ
        (fun γ c => ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c)
        (fun _ c => Pullback.pullVelocity q n a c) (by positivity) hw
        (fun γ o => Pullback.pullList q n a γ o) (fun γ o => (hpcard γ o).trans hκ2)
        (fun γ c => hpmeas γ c) hlst'
    -- the non-full mass is charged to the angular density and the masks
    let Bad : Fin (W (q.sequence.index n)) → Set Inc := fun γ =>
      UWE.angularDensityBad (uweProblem N K d W ω ν E P B f g G) S (q.sequence.index n) γ u τ ∪
        UWE.pureDensityBad (uweProblem N K d W ω ν E P B f g G) (q.sequence.index n) γ 1 τ
    have hNF : ∑ c ∈ NF, wF c ≤
        ENNReal.ofReal (N (q.sequence.index n) ^ (-S * u + 2 * τ) *
          N (q.sequence.index n) ^ (2 * ε) *
          (2 * (2 * N (q.sequence.index n) ^ (2 * ε) *
              (N (q.sequence.index n) ^ (-loss) +
                N (q.sequence.index n) ^ (-w) * N (q.sequence.index n) ^ ε)) /
            δ (N (q.sequence.index n)) u + 2) ^ 2) +
        ENNReal.ofReal (N (q.sequence.index n) ^ (-c₀)) := by
      calc ∑ c ∈ NF, wF c ≤ ∑ c ∈ NF, wH c := Finset.sum_le_sum fun c _ => hFH c
        _ = ∑ γ, ∑ c ∈ NF.filter (fun c => pw c = γ), wH c :=
            (Finset.sum_fiberwise NF pw wH).symm
        _ = ∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
              (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
                (⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c) :=
            Finset.sum_congr rfl fun γ _ => hUmass γ
        _ ≤ ∑ γ, (ENNReal.ofReal (ω (q.sequence.index n) γ) *
              (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
                ((⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c) ∩ (Bad γ)ᶜ) +
            ENNReal.ofReal (ω (q.sequence.index n) γ) *
              (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
                (Bad γ)) := by
            refine Finset.sum_le_sum fun γ _ => ?_
            rw [← mul_add]
            exact mul_le_mul' le_rfl (measure_le_inter_compl_add _ _ _)
        _ = (∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
              (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
                ((⋃ c, ⋃ (_ : ¬ full c ∧ pw c = γ), Hc c) ∩ (Bad γ)ᶜ)) +
            ∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
              (uweProblem N K d W ω ν E P B f g G).incidenceMeasure (q.sequence.index n) γ
                (Bad γ) := Finset.sum_add_distrib
        _ ≤ _ := add_le_add hang hbad
    have hsplit : ∑ c ∈ Sf, wF c + ∑ c ∈ NF, wF c = ∑ c, wF c :=
      Finset.sum_filter_add_sum_filter_not Finset.univ full wF
    have hfull_le : ∑ c ∈ Sf, wF c ≤ ∑ c ∈ Sf, wH c := Finset.sum_le_sum fun c _ => hFH c
    have hNFtop : ∑ c ∈ NF, wF c ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
        hNF
    rw [hRHS]
    refine ENNReal.le_of_add_le_add_right hNFtop ?_
    calc _ ≤ _ + (_ + _) := add_le_add le_rfl hNF
      _ = _ := (add_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal (N (q.sequence.index n) ^ (-ε)) := hnum
      _ ≤ ∑ c, wF c := hcov'
      _ = ∑ c ∈ Sf, wF c + ∑ c ∈ NF, wF c := hsplit.symm
      _ ≤ ∑ c ∈ Sf, wH c + ∑ c ∈ NF, wF c := add_le_add hfull_le le_rfl

end
end RefinedFromAtlas
end Submission.Obl.k4_balanced_native_packet_transport
