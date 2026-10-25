-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterFloors2Lower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterFloors2Lower.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterFloors2Lower.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterFloors2Lower.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4c91e1da. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2
import Submission.Obl.k4_scalar_coefficient_clustering.Bins

/-!
# Parameter-bin floors in version 2 (paper `tex-06`, l. 238–262, lower half)

Paper display `a05:parameter-floor`, lower half: after deleting light coefficient blocks at a
negligible occupation cost, every remaining block `B_p` (all seven coefficients in `p`-bins:
`(x₀, x₁, x₂)`, `y₀ ∈ ℝ²`, `V ∈ ℝ²`) has prior mass `≥ p^(2+d) π([V]_p) N^(-ε)`.  In each
affine-bin world `W = S ∩ {[y₀]_p = β, [V]_p = J}` (prior `ν` restricted, unnormalized, scale
`s = π(J) p²`) the deletion is x0352's `coefficient_floor_cleanup_scaled`
(o106, `ParameterFloor.lean`, scalar clustering of o0xx `k4_scalar_coefficient_clustering`);
its statement enters here as `FloorCleanupStatement` (restated verbatim with `lightBlocks` =
x0352's `lightCoefficientBlocks`), discharged in `ParameterFloors2Heavy.lean`.

* `scalarCoeffPoint K c`: the scalar coefficients `(c 0, c 1, c 2)`, clipped to `[-K, K]`, in `ℝ³`;
* `affine_bin_floor_cleanup`: one affine-bin world;
* `parameter_floor_cleanup`: all affine bins at once, the occupation of the deleted blocks
  bounded by the palette budget `∑ π(J) p² ≤ K_π` times `N^(-η)`.

The masses defining light blocks are those of the FULL prior `ν` on `W` (the frozen long-line
prior `ν°` when `S` is its support), with every extra line tag of `Λ` retained.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open MeasureTheory Set
open Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

/-- Light coefficient blocks: x0352's `lightCoefficientBlocks` (o106, `ParameterFloor.lean`),
restated. -/
def lightBlocks {α : Type*} [MeasurableSpace α] (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3))
    (p : ℝ) (H : ENNReal) : Set α :=
  {l | ν {l' | coefficientCode p (a l') = coefficientCode p (a l)} < H}

/-- The statement of x0352's `coefficient_floor_cleanup_scaled` (o106, `ParameterFloor.lean`). -/
def FloorCleanupStatement (d c ε : ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
      (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3))
      (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)) (s : ENNReal),
      s ≠ 0 → s ≠ ⊤ → Measurable a → MeasurableSet E →
      E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
      (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ s * ENNReal.ofReal (N ^ η) →
      (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
      (∀ l t, (l, t) ∈ E →
        (⌊t / (N ^ (-c))⌋,
          ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) →
      (∀ b r, N ^ (-c) ≤ r →
        ν {l | a l ∈ Metric.ball b r} ≤ s * ENNReal.ofReal (N ^ η * r ^ d)) →
      (ν.prod volume) (E ∩ (lightBlocks ν a (N ^ (-c))
        (s * ENNReal.ofReal (N ^ (-c * d - ε))) ×ˢ Set.univ)) <
        s * ENNReal.ofReal (N ^ (-η))

/-- The scalar coefficients `(c 0, c 1, c 2)` clipped to `[-K, K]`, as a point of `ℝ³`. -/
def scalarCoeffPoint (K : ℝ) (c : Fin 7 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => max (-K) (min K (![c 0, c 1, c 2] i)))

theorem scalarCoeffPoint_apply (K : ℝ) (c : Fin 7 → ℝ) (i : Fin 3) :
    scalarCoeffPoint K c i = max (-K) (min K (![c 0, c 1, c 2] i)) := rfl

theorem measurable_scalarCoeffPoint {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) (K : ℝ) : Measurable (fun l => scalarCoeffPoint K (c l)) := by
  have h0 := (measurable_pi_apply 0).comp hc
  have h1 := (measurable_pi_apply 1).comp hc
  have h2 := (measurable_pi_apply 2).comp hc
  have hpi : Measurable (fun l => fun i : Fin 3 => max (-K) (min K (![c l 0, c l 1, c l 2] i))) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact measurable_const.max (measurable_const.min h0)
    · exact measurable_const.max (measurable_const.min h1)
    · exact measurable_const.max (measurable_const.min h2)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hpi

theorem clip_eq {K x : ℝ} (h : |x| ≤ K) : max (-K) (min K x) = x := by
  have h' := abs_le.mp h
  rw [min_eq_right h'.2, max_eq_right h'.1]

theorem norm_scalarCoeffPoint_le {K : ℝ} (hK : 0 ≤ K) (c : Fin 7 → ℝ) :
    ‖scalarCoeffPoint K c‖ ≤ 2 * K := by
  have hcoord : ∀ i : Fin 3, |scalarCoeffPoint K c i| ≤ K := by
    intro i
    rw [scalarCoeffPoint_apply, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 3, ‖scalarCoeffPoint K c i‖ ^ 2 ≤ (2 * K) ^ 2 := by
    have h : ∀ i : Fin 3, ‖scalarCoeffPoint K c i‖ ^ 2 ≤ K ^ 2 := by
      intro i
      rw [Real.norm_eq_abs, sq_abs]
      have := hcoord i
      nlinarith [abs_nonneg (scalarCoeffPoint K c i), sq_abs (scalarCoeffPoint K c i)]
    calc ∑ i : Fin 3, ‖scalarCoeffPoint K c i‖ ^ 2 ≤ ∑ _i : Fin 3, K ^ 2 :=
          Finset.sum_le_sum fun i _ => h i
      _ = 3 * K ^ 2 := by simp
      _ ≤ (2 * K) ^ 2 := by nlinarith
  calc Real.sqrt (∑ i : Fin 3, ‖scalarCoeffPoint K c i‖ ^ 2) ≤ Real.sqrt ((2 * K) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 * K := Real.sqrt_sq (by positivity)

/-- The affine-bin world of a velocity bin `J` and a position bin `β`. -/
def affineWorld {Λ : Type*} (S : Set Λ) (c : Λ → Fin 7 → ℝ) (p : ℝ) (β J : Fin 2 → ℤ) :
    Set Λ :=
  S ∩ {l | ybin p (c l) = β ∧ vbin p (c l) = J}

theorem measurableSet_affineWorld {Λ : Type*} [MeasurableSpace Λ] {S : Set Λ}
    (hS : MeasurableSet S) {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (p : ℝ) (β J : Fin 2 → ℤ) :
    MeasurableSet (affineWorld S c p β J) :=
  hS.inter (((measurable_ybin hc p) (measurableSet_singleton β)).inter
    ((measurable_vbin hc p) (measurableSet_singleton J)))

/-- **Deleting light blocks in one affine-bin world** (version 2). -/
theorem affine_bin_floor_cleanup {d c ε : ℝ} (hclean : FloorCleanupStatement d c ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsFiniteMeasure ν] (cf : Λ → Fin 7 → ℝ)
        (E : Set (Λ × ℝ)) (S : Set Λ) (K : ℝ) (π : (Fin 2 → ℤ) → ENNReal) (β J : Fin 2 → ℤ)
        (F : Finset (ℤ × ℤ)),
        Measurable cf → MeasurableSet E → E ⊆ univ ×ˢ Icc (0 : ℝ) 1 → MeasurableSet S →
        0 ≤ K → 2 * K ≤ N ^ η → π J ≠ 0 → π J ≠ ⊤ →
        (∀ l ∈ S, |cf l 0| ≤ K ∧ |cf l 1| ≤ K ∧ |cf l 2| ≤ K) →
        ν (affineWorld S cf (N ^ (-c)) β J) ≤
          π J * ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ η) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
          ν (affineWorld S cf (N ^ (-c)) β J ∩ {l | scalarCoeffPoint K (cf l) ∈ Metric.ball b r}) ≤
            π J * ENNReal.ofReal ((N ^ (-c)) ^ 2 * (N ^ η * r ^ d))) →
        (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
        (∀ l t, (l, t) ∈ E → l ∈ affineWorld S cf (N ^ (-c)) β J →
          (⌊t / N ^ (-c)⌋, ⌊zx (cf l) t / N ^ (-c)⌋) ∈ F) →
        (ν.prod volume) (E ∩ ((affineWorld S cf (N ^ (-c)) β J ∩
          lightBlocks (ν.restrict (affineWorld S cf (N ^ (-c)) β J))
            (fun l => scalarCoeffPoint K (cf l)) (N ^ (-c))
            (π J * ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ (-c * d - ε)))) ×ˢ univ)) <
          π J * ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ (-η)) := by
  obtain ⟨η, hη, N₀, hN₀, h⟩ := hclean
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN Λ _ ν _ cf E S K π β J F hcf hE hunit hS hK0 hKN hπ0 hπtop hcoeff hmass hcap hFcard hF
  set p := N ^ (-c) with hpdef
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hN₀.trans hN)
  have hp : 0 < p := Real.rpow_pos_of_pos hNpos _
  set W := affineWorld S cf p β J with hWdef
  have hW : MeasurableSet W := measurableSet_affineWorld hS hcf p β J
  set s : ENNReal := π J * ENNReal.ofReal (p ^ 2) with hsdef
  have hs0 : s ≠ 0 := mul_ne_zero hπ0 (by simp [ENNReal.ofReal_eq_zero]; positivity)
  have hstop : s ≠ ⊤ := ENNReal.mul_ne_top hπtop ENNReal.ofReal_ne_top
  have hsmul : ∀ x : ℝ, 0 ≤ x → s * ENNReal.ofReal x = π J * ENNReal.ofReal (p ^ 2 * x) := by
    intro x hx
    rw [hsdef, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  let a : Λ → EuclideanSpace ℝ (Fin 3) := fun l => scalarCoeffPoint K (cf l)
  have ha : Measurable a := measurable_scalarCoeffPoint hcf K
  let E' := E ∩ (W ×ˢ univ)
  have hE' : MeasurableSet E' := hE.inter (hW.prod MeasurableSet.univ)
  have hE'unit : E' ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun z hz => hunit hz.1
  have hnorm : ∀ l, ‖a l‖ ≤ N ^ η := fun l => (norm_scalarCoeffPoint_le hK0 _).trans hKN
  have hmass' : (ν.restrict W) univ ≤ s * ENNReal.ofReal (N ^ η) := by
    rw [Measure.restrict_apply_univ, hsmul _ (Real.rpow_nonneg hNpos.le _)]
    exact hmass
  have hsupp : ∀ l t, (l, t) ∈ E' →
      (⌊t / p⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / p⌋) ∈ F := by
    intro l t hlt
    have hlW : l ∈ W := hlt.2.1
    obtain ⟨h0, h1, h2⟩ := hcoeff l hlW.1
    have e0 : a l 0 = cf l 0 := by
      show max (-K) (min K (![cf l 0, cf l 1, cf l 2] 0)) = cf l 0
      simpa using clip_eq h0
    have e1 : a l 1 = cf l 1 := by
      show max (-K) (min K (![cf l 0, cf l 1, cf l 2] 1)) = cf l 1
      simpa using clip_eq h1
    have e2 : a l 2 = cf l 2 := by
      show max (-K) (min K (![cf l 0, cf l 1, cf l 2] 2)) = cf l 2
      simpa using clip_eq h2
    have hx : a l 0 + t * a l 1 + t ^ 2 * a l 2 = zx (cf l) t := by
      rw [e0, e1, e2]; simp only [zx]; ring
    rw [hx]
    exact hF l t hlt.1 hlW
  have hcap' : ∀ b r, p ≤ r →
      (ν.restrict W) {l | a l ∈ Metric.ball b r} ≤ s * ENNReal.ofReal (N ^ η * r ^ d) := by
    intro b r hr
    have hmeas : MeasurableSet {l | a l ∈ Metric.ball b r} := ha Metric.isOpen_ball.measurableSet
    rw [Measure.restrict_apply hmeas, inter_comm,
      hsmul _ (mul_nonneg (Real.rpow_nonneg hNpos.le _)
        (Real.rpow_nonneg (hp.le.trans hr) _))]
    exact hcap b r hr
  have hmain := h N hN Λ (ν.restrict W) a E' F s hs0 hstop ha hE' hE'unit hnorm hmass' hFcard
    hsupp hcap'
  have hprod : ((ν.restrict W).prod volume)
      (E' ∩ (lightBlocks (ν.restrict W) a p (s * ENNReal.ofReal (N ^ (-c * d - ε))) ×ˢ univ)) =
      (ν.prod volume) (E ∩ ((W ∩ lightBlocks (ν.restrict W) a p
        (s * ENNReal.ofReal (N ^ (-c * d - ε)))) ×ˢ univ)) := by
    rw [Measure.restrict_prod_eq_prod_univ W]
    have hset : E' ∩ (lightBlocks (ν.restrict W) a p (s * ENNReal.ofReal (N ^ (-c * d - ε))) ×ˢ univ)
        ∩ (W ×ˢ univ) = E ∩ ((W ∩ lightBlocks (ν.restrict W) a p
          (s * ENNReal.ofReal (N ^ (-c * d - ε)))) ×ˢ univ) := by
      ext z
      simp only [E', mem_inter_iff, mem_prod, mem_univ, and_true]
      tauto
    have hlightm : MeasurableSet (lightBlocks (ν.restrict W) a p
        (s * ENNReal.ofReal (N ^ (-c * d - ε)))) := by
      let Q : Set (Fin 3 → ℤ) := {q | (ν.restrict W) {l | coefficientCode p (a l) = q} <
        s * ENNReal.ofReal (N ^ (-c * d - ε))}
      exact ((measurable_coefficientCode p).comp ha) ((Set.to_countable Q).measurableSet)
    rw [Measure.restrict_apply (hE'.inter (hlightm.prod MeasurableSet.univ)), hset]
  rw [hprod] at hmain
  have hlight : s * ENNReal.ofReal (N ^ (-c * d - ε)) =
      π J * ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ (-c * d - ε)) :=
    hsmul _ (Real.rpow_nonneg hNpos.le _)
  have hfinal : s * ENNReal.ofReal (N ^ (-η)) = π J * ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ (-η)) :=
    hsmul _ (Real.rpow_nonneg hNpos.le _)
  rw [hlight, hfinal] at hmain
  exact hmain

/-- The deleted part of one affine-bin world: its light blocks. -/
def lightPart {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (cf : Λ → Fin 7 → ℝ) (S : Set Λ)
    (K p : ℝ) (π : (Fin 2 → ℤ) → ENNReal) (h : ℝ) (β J : Fin 2 → ℤ) : Set Λ :=
  affineWorld S cf p β J ∩ lightBlocks (ν.restrict (affineWorld S cf p β J))
    (fun l => scalarCoeffPoint K (cf l)) p (π J * ENNReal.ofReal (p ^ 2 * h))

/-- **Deleting light blocks in all affine-bin worlds** (version 2): the deleted occupation is at
most the palette budget times `N^(-η)`, and every remaining line of `S` lies in a block of full
prior mass `≥ π([V]_p) p^(2+d) N^(-ε)` inside its affine-bin world. -/
theorem parameter_floor_cleanup {d c ε : ℝ} (hclean : FloorCleanupStatement d c ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsFiniteMeasure ν]
        (cf : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) (S : Set Λ) (K Kπ : ℝ)
        (π : (Fin 2 → ℤ) → ENNReal) (A2 : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
        (F : (Fin 2 → ℤ) → (Fin 2 → ℤ) → Finset (ℤ × ℤ)),
        Measurable cf → MeasurableSet E → E ⊆ univ ×ˢ Icc (0 : ℝ) 1 → MeasurableSet S →
        0 ≤ K → 2 * K ≤ N ^ η → 0 ≤ Kπ →
        (∀ l ∈ S, (ybin (N ^ (-c)) (cf l), vbin (N ^ (-c)) (cf l)) ∈ A2) →
        (∑ βJ ∈ A2, π βJ.2 * ENNReal.ofReal ((N ^ (-c)) ^ 2)) ≤ ENNReal.ofReal Kπ →
        (∀ l ∈ S, |cf l 0| ≤ K ∧ |cf l 1| ≤ K ∧ |cf l 2| ≤ K) →
        (∀ βJ ∈ A2, ν (affineWorld S cf (N ^ (-c)) βJ.1 βJ.2) ≤
          π βJ.2 * ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ η)) →
        (∀ βJ ∈ A2, ∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
          ν (affineWorld S cf (N ^ (-c)) βJ.1 βJ.2 ∩
            {l | scalarCoeffPoint K (cf l) ∈ Metric.ball b r}) ≤
            π βJ.2 * ENNReal.ofReal ((N ^ (-c)) ^ 2 * (N ^ η * r ^ d))) →
        (∀ βJ ∈ A2, ((F βJ.1 βJ.2).card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d)) →
        (∀ βJ ∈ A2, ∀ l t, (l, t) ∈ E → l ∈ affineWorld S cf (N ^ (-c)) βJ.1 βJ.2 →
          (⌊t / N ^ (-c)⌋, ⌊zx (cf l) t / N ^ (-c)⌋) ∈ F βJ.1 βJ.2) →
        (ν.prod volume) (E ∩ ((⋃ βJ ∈ A2, lightPart ν cf S K (N ^ (-c)) π
            (N ^ (-c * d - ε)) βJ.1 βJ.2) ×ˢ univ)) ≤
          ENNReal.ofReal Kπ * ENNReal.ofReal (N ^ (-η)) ∧
        ∀ l ∈ S, l ∉ (⋃ βJ ∈ A2, lightPart ν cf S K (N ^ (-c)) π
            (N ^ (-c * d - ε)) βJ.1 βJ.2) →
          π (vbin (N ^ (-c)) (cf l)) *
              ENNReal.ofReal ((N ^ (-c)) ^ 2 * N ^ (-c * d - ε)) ≤
            ν ({l' | coefficientCode (N ^ (-c)) (scalarCoeffPoint K (cf l')) =
                coefficientCode (N ^ (-c)) (scalarCoeffPoint K (cf l))} ∩
              affineWorld S cf (N ^ (-c)) (ybin (N ^ (-c)) (cf l)) (vbin (N ^ (-c)) (cf l))) := by
  obtain ⟨η, hη, N₀, hN₀, hone⟩ := affine_bin_floor_cleanup hclean
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN Λ _ ν _ cf E S K Kπ π A2 F hcf hE hunit hS hK0 hKN hKπ hA2 hpal hcoeff hmass hcap
    hFcard hF
  set p := N ^ (-c) with hpdef
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hN₀.trans hN)
  have hp : 0 < p := Real.rpow_pos_of_pos hNpos _
  have hp2 : ENNReal.ofReal (p ^ 2) ≠ 0 := by simp [ENNReal.ofReal_eq_zero]; positivity
  have hnη : 0 ≤ N ^ (-η) := Real.rpow_nonneg hNpos.le _
  -- one bin
  have hbin : ∀ βJ ∈ A2, (ν.prod volume) (E ∩ (lightPart ν cf S K p π (N ^ (-c * d - ε))
      βJ.1 βJ.2 ×ˢ univ)) ≤ π βJ.2 * ENNReal.ofReal (p ^ 2) * ENNReal.ofReal (N ^ (-η)) := by
    intro βJ hβJ
    have hscale : π βJ.2 * ENNReal.ofReal (p ^ 2) * ENNReal.ofReal (N ^ (-η)) =
        π βJ.2 * ENNReal.ofReal (p ^ 2 * N ^ (-η)) := by
      rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [hscale]
    by_cases hπ0 : π βJ.2 = 0
    · -- an empty world
      have hW0 : ν (affineWorld S cf p βJ.1 βJ.2) = 0 := by
        have := hmass βJ hβJ
        rw [hπ0, zero_mul] at this
        exact le_antisymm this bot_le
      have hsub : E ∩ (lightPart ν cf S K p π (N ^ (-c * d - ε)) βJ.1 βJ.2 ×ˢ univ) ⊆
          affineWorld S cf p βJ.1 βJ.2 ×ˢ univ := fun z hz => ⟨hz.2.1.1, mem_univ _⟩
      calc (ν.prod volume) (E ∩ (lightPart ν cf S K p π (N ^ (-c * d - ε)) βJ.1 βJ.2 ×ˢ univ))
          ≤ (ν.prod volume) (affineWorld S cf p βJ.1 βJ.2 ×ˢ univ) := measure_mono hsub
        _ = 0 := by rw [Measure.prod_prod, hW0, zero_mul]
        _ ≤ _ := bot_le
    · have hπtop : π βJ.2 ≠ ⊤ := by
        intro htop
        have hle : π βJ.2 * ENNReal.ofReal (p ^ 2) ≤ ENNReal.ofReal Kπ :=
          (Finset.single_le_sum (f := fun βJ => π βJ.2 * ENNReal.ofReal (p ^ 2))
            (fun _ _ => bot_le) hβJ).trans hpal
        rw [htop, ENNReal.top_mul hp2] at hle
        exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)
      exact (hone N hN Λ ν cf E S K π βJ.1 βJ.2 (F βJ.1 βJ.2) hcf hE hunit hS hK0 hKN hπ0 hπtop
        hcoeff (hmass βJ hβJ) (hcap βJ hβJ) (hFcard βJ hβJ) (hF βJ hβJ)).le
  refine ⟨?_, ?_⟩
  · have hunion : E ∩ ((⋃ βJ ∈ A2, lightPart ν cf S K p π (N ^ (-c * d - ε)) βJ.1 βJ.2) ×ˢ univ) =
        ⋃ βJ ∈ A2, E ∩ (lightPart ν cf S K p π (N ^ (-c * d - ε)) βJ.1 βJ.2 ×ˢ univ) := by
      ext z
      simp only [mem_inter_iff, mem_prod, mem_iUnion, mem_univ, and_true, exists_prop]
      tauto
    rw [hunion]
    calc (ν.prod volume) (⋃ βJ ∈ A2, E ∩ (lightPart ν cf S K p π (N ^ (-c * d - ε))
          βJ.1 βJ.2 ×ˢ univ))
        ≤ ∑ βJ ∈ A2, (ν.prod volume) (E ∩ (lightPart ν cf S K p π (N ^ (-c * d - ε))
          βJ.1 βJ.2 ×ˢ univ)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ βJ ∈ A2, π βJ.2 * ENNReal.ofReal (p ^ 2) * ENNReal.ofReal (N ^ (-η)) :=
          Finset.sum_le_sum hbin
      _ = (∑ βJ ∈ A2, π βJ.2 * ENNReal.ofReal (p ^ 2)) * ENNReal.ofReal (N ^ (-η)) := by
          rw [Finset.sum_mul]
      _ ≤ ENNReal.ofReal Kπ * ENNReal.ofReal (N ^ (-η)) := mul_le_mul' hpal le_rfl
  · intro l hl hnot
    set β := ybin p (cf l)
    set J := vbin p (cf l)
    have hmem := hA2 l hl
    have hlW : l ∈ affineWorld S cf p β J := ⟨hl, rfl, rfl⟩
    have hnl : l ∉ lightBlocks (ν.restrict (affineWorld S cf p β J))
        (fun l => scalarCoeffPoint K (cf l)) p (π J * ENNReal.ofReal (p ^ 2 * N ^ (-c * d - ε))) := by
      intro hlight
      exact hnot (mem_iUnion₂.mpr ⟨(β, J), hmem, hlW, hlight⟩)
    simp only [lightBlocks, mem_ofPred_eq, not_lt] at hnl
    have hX : MeasurableSet {l' | coefficientCode p (scalarCoeffPoint K (cf l')) =
        coefficientCode p (scalarCoeffPoint K (cf l))} :=
      ((measurable_coefficientCode p).comp (measurable_scalarCoeffPoint hcf K))
        (measurableSet_singleton _)
    rw [Measure.restrict_apply hX] at hnl
    exact hnl


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
