import Submission.Obl.k4_general_parent_projected_layers.Combine
import Submission.Obl.k4_general_parent_projected_layers.Raw
import Submission.Obl.k4_general_parent_projected_layers.ScalarPackets
import Submission.Obl.k4_general_parent_projected_layers.Transverse

/-!
# Scalar on every prepared world, restored and merged into one layer

A `ScalarWorld` is one original group (a crop of trajectories with fixed mesh tags of
`b3, b0` and a transverse crop center), with its scalar coefficients. When it is
`Ready` (Scalar's input holds for its conditioned law), Scalar's packets are trimmed to
the crop and restored to physical coordinates: width `g β`, lines `y + g u`, and
quadratic `transversePullback`. All floors are under the original residual.
`layer_of_worlds` then merges one width class of all ready worlds into one layer.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery (scalarY scalarX scalarCell)
open Submission.Obl.k4_horizontal_supercritical_three_projections
  (chartLaw chartLaw_supported)

noncomputable section

/-- One original world: a crop of trajectories, its mesh tags, its transverse crop
center, and its (padded) scalar coefficients. -/
structure ScalarWorld (α : Type) where
  crop : Set α
  tag : Fin 2 → ℤ
  y₀ : ℝ
  y₁ : ℝ
  coeff : α → Fin 5 → ℝ

namespace ScalarWorld

variable {α : Type} [MeasurableSpace α]

/-- The world's normalized scalar parameter: mesh, crop width and palette over prior. -/
def param (w : ScalarWorld α) (χ g : ℝ) (ν : Measure α) (π : Measure ℝ) : ℝ :=
  χ * g * (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal / (ν w.crop).toReal

/-- A world ready for Scalar at loss exponent `η`: its geometry, the exact scalar
coordinates on its crop, and Scalar's input for its conditioned current law. -/
structure Ready (w : ScalarWorld α) (N η d s M C χ g K : ℝ) (b : α → Fin 6 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (ν : Measure α) (π : Measure ℝ)
    (ζ : Measure (α × ℝ)) : Prop where
  measurable : MeasurableSet w.crop
  prior : ν w.crop ≠ 0
  tags : ∀ l ∈ w.crop, ⌊b l 3 / χ⌋ = w.tag 0 ∧ ⌊b l 0 / χ⌋ = w.tag 1
  center : |w.y₀| + |w.y₁| ≤ K
  coeff_y : ∀ l ∈ w.crop, ∀ t : ℝ, scalarY (w.coeff l) t =
    ((Submission.Lib.K4ContactNormalization.point (b l) t) 2 - w.y₀ - t * w.y₁) / g
  coeff_x : ∀ l ∈ w.crop, ∀ t : ℝ, scalarX (w.coeff l) t =
    eval (Submission.Lib.K4ContactNormalization.point (b l) t) P
  input : ScalarInput N η d s M C (w.param χ g ν π) (ProbabilityTheory.cond ν w.crop)
    (chartLaw ν ζ w.crop) w.coeff
  dense : ENNReal.ofReal (N ^ (-η)) ≤ chartLaw ν ζ w.crop univ

/-- The restored physical layer of Scalar's packets on one world. -/
def layer (w : ScalarWorld α) (g : ℝ) {N d s M c ε : ℝ} {μ : Measure (α × ℝ)}
    (F : ScalarPackets N d s M c ε μ w.coeff) : ProjLayer α where
  n := F.n
  β := g * F.beta
  C := fun i => F.A i ∩ w.crop
  tag := fun _ => w.tag
  u := fun i => w.y₀ + g * F.u i
  v := fun i => w.y₁ + g * F.v i
  G := fun i => transversePullback w.y₀ w.y₁ g (F.P i)

theorem layer_C_subset (w : ScalarWorld α) (g : ℝ) {N d s M c ε : ℝ}
    {μ : Measure (α × ℝ)} (F : ScalarPackets N d s M c ε μ w.coeff) (i : Fin F.n) :
    (w.layer g F).C i ⊆ w.crop := inter_subset_right

/-- Restored floors and fits of one ready world, and its restored covered mass. -/
theorem layer_good (w : ScalarWorld α) {N η d s M C χ g K ell La ε : ℝ}
    {b : α → Fin 6 → ℝ} {P : MvPolynomial (Fin 4) ℝ} {ν : Measure α}
    [IsProbabilityMeasure ν] {π : Measure ℝ} [IsFiniteMeasure π]
    {ζ ρ : Measure (α × ℝ)}
    (hw : w.Ready N η d s M C χ g K b P ν π ζ) (hζρ : ζ ≤ ρ)
    (hN : 1 ≤ N) (hχ : 0 ≤ χ) (hg : g = N ^ (-ell * s)) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hMLa : M ≤ La)
    (F : ScalarPackets N d s M (w.param χ g ν π) ε (chartLaw ν ζ w.crop) w.coeff) :
    (w.layer g F).Good N (K + N ^ ε) d ell La s χ b P π ρ ∧
      ENNReal.ofReal ((ν w.crop).toReal * N ^ (-ε)) ≤ ζ (w.layer g F).covered := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hg0 : 0 < g := hg ▸ Real.rpow_pos_of_pos hN0 _
  have hpow0 : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 ε
  have hE : N ^ ε ≤ K + N ^ ε := le_add_of_nonneg_left hK
  have hE0 : 0 < K + N ^ ε := hpow0.trans_le hE
  have hβ := F.beta_pos hN0
  have hNs : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN0.le _
  -- trim to the crop, then restore floors and mass to the current law
  let F' := F.trim hw.measurable (chartLaw_supported ν ζ hw.measurable) (fun _ _ => rfl)
  obtain ⟨hfloor, hmass⟩ := ScalarPackets.restore ν ζ w.crop hw.prior w.coeff F'
  refine ⟨⟨mul_pos hg0 hβ, ?_, ?_, ?_, ?_, ?_⟩, hmass⟩
  · -- lower width bound
    have hlo : N ^ (-M) / N ^ ε ≤ F.beta := F.beta_lower
    have h1 : N ^ (-La) ≤ N ^ (-M) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    rw [← hg]
    calc g * N ^ (-La) / (K + N ^ ε) ≤ g * N ^ (-M) / N ^ ε := by
          apply div_le_div₀ (mul_nonneg hg0.le (Real.rpow_nonneg hN0.le _))
            (mul_le_mul_of_nonneg_left h1 hg0.le) hpow0 hE
      _ = g * (N ^ (-M) / N ^ ε) := by ring
      _ ≤ g * F.beta := mul_le_mul_of_nonneg_left hlo hg0.le
  · rw [← hg]
    show g * F.beta ≤ (K + N ^ ε) * g
    rw [mul_comm g]
    exact mul_le_mul_of_nonneg_right (F.beta_upper.trans hE) hg0.le
  · intro i
    exact (F.measurable i).inter hw.measurable
  · intro i i' hii'
    exact (F.disjoint i i' hii').mono inter_subset_left inter_subset_left
  · intro i
    refine ⟨?_, (transversePullback_degree _ _ _ _).trans (F.degree i), ?_, ?_, ?_⟩
    · -- restored centers
      have h := transverse_centers_bound hg0.le hw.center (F.centers i)
      calc |w.y₀ + g * F.u i| + |w.y₁ + g * F.v i| ≤ K + g * N ^ ε := h
        _ ≤ K + N ^ ε := by
          have : g * N ^ ε ≤ N ^ ε := by
            calc g * N ^ ε ≤ 1 * N ^ ε := mul_le_mul_of_nonneg_right hg1 hpow0.le
              _ = N ^ ε := one_mul _
          linarith
    · intro t ht v hv
      exact (transversePullback_adapted_bound w.y₀ w.y₁ hg0.ne' (F.P i) (F.u i) (F.v i)
        F.beta (N ^ ε) (F.norm i) t ht v hv).trans hE
    · intro l hl
      refine ⟨(hw.tags l hl.2).1, (hw.tags l hl.2).2, fun t ht => ?_⟩
      obtain ⟨hy, hx⟩ := F.fit i l hl.1 t ht
      rw [hw.coeff_y l hl.2 t] at hy hx
      rw [hw.coeff_x l hl.2 t] at hx
      refine ⟨?_, ?_⟩
      · have h := transverse_interval_error w.y₀ w.y₁ hg0 _ t (F.u i) (F.v i) F.beta
          (N ^ ε) hy
        exact h.trans (mul_le_mul_of_nonneg_right hE (mul_pos hg0 hβ).le)
      · show |eval (Submission.Lib.K4ContactNormalization.point (b l) t) P -
          eval ![t, (Submission.Lib.K4ContactNormalization.point (b l) t) 2]
            (transversePullback w.y₀ w.y₁ g (F.P i))| ≤ (K + N ^ ε) * N ^ (-s)
        rw [eval_transversePullback]
        exact hx.trans (mul_le_mul_of_nonneg_right hE hNs)
    · -- restored floor under the original residual
      refine le_trans ?_ ((hfloor i).trans (hζρ _))
      change ENNReal.ofReal (χ * (N ^ (-s)) ^ d * (g * F.beta) / (K + N ^ ε)) *
          π {v : ℝ | ⌊v / χ⌋ = w.tag 0} ≤
        ENNReal.ofReal (χ * g * (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal *
          (N ^ (-s)) ^ d * F.beta / N ^ ε)
      have hπ : ENNReal.ofReal (χ * (N ^ (-s)) ^ d * (g * F.beta) / (K + N ^ ε)) *
          π {v : ℝ | ⌊v / χ⌋ = w.tag 0} =
          ENNReal.ofReal (χ * (N ^ (-s)) ^ d * (g * F.beta) / (K + N ^ ε) *
            (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top π _)]
      rw [hπ]
      apply ENNReal.ofReal_le_ofReal
      have hπ0 : 0 ≤ (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal := ENNReal.toReal_nonneg
      have hA : 0 ≤ χ * (N ^ (-s)) ^ d * (g * F.beta) * (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal :=
        by positivity
      calc χ * (N ^ (-s)) ^ d * (g * F.beta) / (K + N ^ ε) *
            (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal
          = χ * (N ^ (-s)) ^ d * (g * F.beta) *
              (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal / (K + N ^ ε) := by ring
        _ ≤ χ * (N ^ (-s)) ^ d * (g * F.beta) *
              (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal / N ^ ε :=
            div_le_div_of_nonneg_left hA hpow0 hE
        _ = χ * g * (π {v : ℝ | ⌊v / χ⌋ = w.tag 0}).toReal *
              (N ^ (-s)) ^ d * F.beta / N ^ ε := by ring

end ScalarWorld

/-- Scalar on every ready world, restored and merged: one layer of common width that
carries a `1 / #classes` share of the restored mass `ν(crop) N^(-ε)` of all worlds. -/
theorem layer_of_worlds (hScalar : Scalar) {d s M C ε τ : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsM : s < M) (hC : 0 < C) (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
        (π : Measure ℝ) [IsFiniteMeasure π] (ζ ρ : Measure (α × ℝ))
        (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (ι : Type) [DecidableEq ι]
        (Q : Finset ι) (W : ι → ScalarWorld α) (χ g K ell La : ℝ),
        ζ ≤ ρ → 0 ≤ χ → g = N ^ (-ell * s) → g ≤ 1 → 0 ≤ K → M ≤ La →
        (∀ u ∈ Q, (W u).Ready N η d s M C χ g K b P ν π ζ) →
        (∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → Disjoint (W u).crop (W u').crop) →
        ∃ L : ProjLayer α, L.Good N ((K + N ^ ε) * N ^ τ) d ell La s χ b P π ρ ∧
          (∑ u ∈ Q, ENNReal.ofReal ((ν (W u).crop).toReal * N ^ (-ε))) ≤
            ((widthIndices (M + ε) ε τ).card : ENNReal) * ζ L.covered := by
  classical
  obtain ⟨η, hη, N₀, hN₀, H⟩ := scalar_packets_of_mesh hScalar hd hd1 hs hsM hC hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν _ π _ ζ ρ b P ι _ Q W χ g K ell La hζρ hχ hg hg1 hK hMLa hready hdisj
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  have hpackets : ∀ u ∈ Q, Nonempty (ScalarPackets N d s M ((W u).param χ g ν π) ε
      (chartLaw ν ζ (W u).crop) (W u).coeff) := fun u hu =>
    H N hN α (ProbabilityTheory.cond ν (W u).crop) (chartLaw ν ζ (W u).crop) (W u).coeff
      ((W u).param χ g ν π) (hready u hu).input (hready u hu).dense
  let L : ι → ProjLayer α := fun u =>
    if hu : u ∈ Q then (W u).layer g (Classical.choice (hpackets u hu)) else ProjLayer.empty
  have hL : ∀ u (hu : u ∈ Q), L u = (W u).layer g (Classical.choice (hpackets u hu)) :=
    fun u hu => dif_pos hu
  have hgood : ∀ u ∈ Q, (L u).Good N (K + N ^ ε) d ell La s χ b P π ρ ∧
      ENNReal.ofReal ((ν (W u).crop).toReal * N ^ (-ε)) ≤ ζ (L u).covered := by
    intro u hu
    rw [hL u hu]
    exact ScalarWorld.layer_good (W u) (hready u hu) hζρ hN1.le hχ hg hg1 hK hMLa _
  have hsub : ∀ u ∈ Q, ∀ i, (L u).C i ⊆ (W u).crop := by
    intro u hu
    have h := hL u hu
    generalize L u = L' at h ⊢
    subst h
    exact ScalarWorld.layer_C_subset _ _ _
  have hdisj' : ∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → ∀ i i', Disjoint ((L u).C i) ((L u').C i') := by
    intro u hu u' hu' huu i i'
    exact (hdisj u hu u' hu' huu).mono (hsub u hu i) (hsub u' hu' i')
  have hwidth : ∀ u ∈ Q, N ^ (-(M + ε)) ≤ (L u).β / N ^ (-ell * s) ∧
      (L u).β / N ^ (-ell * s) ≤ N ^ ε := by
    intro u hu
    have hg0 : 0 < g := hg ▸ Real.rpow_pos_of_pos hN0 _
    rw [hL u hu, ← hg]
    set F := Classical.choice (hpackets u hu)
    have hβ : ((W u).layer g F).β = g * F.beta := rfl
    rw [hβ, mul_div_cancel_left₀ _ hg0.ne']
    refine ⟨?_, F.beta_upper⟩
    have h := F.beta_lower
    rwa [neg_add, Real.rpow_add hN0, Real.rpow_neg hN0.le ε, ← div_eq_mul_inv]
  have hLa : 0 ≤ La := by linarith
  have hE : 1 ≤ K + N ^ ε := by
    have := Real.one_le_rpow hN1.le hε.le
    linarith
  obtain ⟨L', hL'good, hL'mass⟩ := ProjLayer.exists_merged_layer Q L ζ hN1 hτ hE hχ hLa hdisj'
    (fun u hu => (hgood u hu).1) hwidth
  exact ⟨L', hL'good, (Finset.sum_le_sum fun u hu => (hgood u hu).2).trans hL'mass⟩

end

end Submission.Obl.k4_general_parent_projected_layers
