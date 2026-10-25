/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/RootMeshControl.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootPartition
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.MeshCoefficientPowers
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.PolynomialBallControl

/-! The exact-root partition follows from finite base-mesh caps. -/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh

open Submission.Lib.K4AffineMeshCaps

open MvPolynomial MeasureTheory Set
open Submission.Obl.k4_stable_native_signal_oscillation (erBase)

noncomputable section

def rootBaseCoordinates (p : EuclideanSpace ℝ (Fin 4)) : Fin 3 → ℝ := fun i => erBase p i

def RootBaseSmall (μ : Measure (EuclideanSpace ℝ (Fin 4))) : Prop :=
  ∀ᵐ p ∂μ, rootBaseCoordinates p ∈
    Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4)

def RootMeshCap (μ : Measure (EuclideanSpace ℝ (Fin 4))) (K delta : ℝ) : Prop :=
  ∀ q : Fin 3 → ℤ,
    μ {p | baseMesh delta (rootBaseCoordinates p) = q} ≤ ENNReal.ofReal (K * delta ^ 3)

theorem root_polynomial_control_from_mesh :
    ∃ J N : ℕ, 4 ≤ J ∧ 1 ≤ N ∧
      ∀ K delta : ℝ, 2 ≤ K → 0 < delta → delta ≤ (K ^ J)⁻¹ →
        ∀ μ : Measure (EuclideanSpace ℝ (Fin 4)), IsProbabilityMeasure μ →
          RootBaseSmall μ → RootMeshCap μ K delta → RootPolynomialControl μ K N := by
  obtain ⟨J, n, hJ, hn, hcoef⟩ := mesh_coefficient_power_control 4 0
  obtain ⟨N, hN, hball⟩ := coefficient_power_ball_control 4 n
  refine ⟨J, N, hJ, hN, ?_⟩
  intro K delta hK hd hdJ μ hprob hbase hcap G hG _hGball f hf V hV hfG
  haveI : IsProbabilityMeasure μ := hprob
  let T : Set (Fin 3 → ℝ) :=
    Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) ∩ {z | |eval z f| ≤ V}
  have hfull : ∀ᵐ p ∂μ, rootBaseCoordinates p ∈ T ∧ True := by
    filter_upwards [hbase, hG] with p hp hpG
    exact ⟨⟨hp, hfG p hpG⟩, trivial⟩
  have hevent : μ {p | rootBaseCoordinates p ∈ T ∧ True} = 1 := by
    have heq : {p | rootBaseCoordinates p ∈ T ∧ True} =ᵐ[μ] univ := by
      filter_upwards [hfull] with p hp
      change (rootBaseCoordinates p ∈ T ∧ True) = True
      exact propext (iff_true_intro hp)
    rw [measure_congr heq]
    exact measure_univ
  have hmass : ENNReal.ofReal ((K ^ (0 : ℕ))⁻¹) ≤
      μ {p | rootBaseCoordinates p ∈ T ∧ True} := by
    rw [hevent]
    simp
  have hcap' (q : Fin 3 → ℤ) :
      μ {p | baseMesh delta (rootBaseCoordinates p) = q ∧ True} ≤
        ENNReal.ofReal (K * delta ^ 3) := by simpa using hcap q
  have hcoeff := hcoef K delta hK hd hdJ (EuclideanSpace ℝ (Fin 4)) μ
    rootBaseCoordinates (fun _ => True) hcap' T inter_subset_left hmass V hV f hf
    (fun z hz => hz.2)
  exact hball K V hK hV f hf hcoeff

theorem root_slab_control_from_mesh (A : ℕ) :
    ∃ J c : ℕ, 4 ≤ J ∧
      ∀ K delta : ℝ, 2 ≤ K → 0 < delta → delta ≤ (K ^ J)⁻¹ →
        ∀ μ : Measure (EuclideanSpace ℝ (Fin 4)),
          RootBaseSmall μ → RootMeshCap μ K delta → RootSlabControl μ K A c := by
  obtain ⟨J, n, hJ, hn, hcoef⟩ := mesh_coefficient_power_control 4 A
  obtain ⟨N, hN, hball⟩ := coefficient_power_ball_control 4 n
  refine ⟨J, N + 1, hJ, ?_⟩
  intro K delta hK hd hdJ μ hbase hcap B hB x₀ hx₀ _hmax hpos
  have hK0 : 0 < K := by linarith
  let b : ℝ := |eval (fun i => x₀ i) B|
  let V : ℝ := b / K ^ (N + 1)
  let T : Set (Fin 3 → ℝ) := {z |
    z ∈ Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) ∧
      ‖WithLp.toLp 2 z‖ ≤ K ∧ |eval z B| ≤ V}
  have hV : 0 ≤ V := by dsimp [V, b]; positivity
  by_contra hbad
  have hmass : ENNReal.ofReal ((K ^ A)⁻¹) ≤
      μ (erBase ⁻¹' {x | ‖x‖ ≤ K ∧ |eval (fun i => x i) B| ≤ V}) :=
    le_of_lt (lt_of_not_ge hbad)
  have heq : {p | rootBaseCoordinates p ∈ T ∧ True} =ᵐ[μ]
      erBase ⁻¹' {x | ‖x‖ ≤ K ∧ |eval (fun i => x i) B| ≤ V} := by
    filter_upwards [hbase] with p hp
    simp only [T, mem_setOf_eq, mem_preimage, hp, true_and, and_true]
    rfl
  have hmass' : ENNReal.ofReal ((K ^ A)⁻¹) ≤
      μ {p | rootBaseCoordinates p ∈ T ∧ True} :=
    hmass.trans_eq (measure_congr heq).symm
  have hcap' (q : Fin 3 → ℤ) :
      μ {p | baseMesh delta (rootBaseCoordinates p) = q ∧ True} ≤
        ENNReal.ofReal (K * delta ^ 3) := by simpa using hcap q
  have hcoeff := hcoef K delta hK hd hdJ (EuclideanSpace ℝ (Fin 4)) μ
    rootBaseCoordinates (fun _ => True) hcap' T (fun z hz => hz.1) hmass' V hV B hB
    (fun z hz => hz.2.2)
  have hanchor : b ≤ K ^ N * V := (hball K V hK hV B hB hcoeff).1 x₀ (by linarith)
  have hratio : K ^ N * V = b / K := by
    dsimp [V]
    rw [pow_succ]
    field_simp
  have hlt : b / K < b := by
    apply (div_lt_iff₀ hK0).mpr
    dsimp [b]
    nlinarith
  exact (not_le_of_gt hlt) (hanchor.trans_eq hratio)

/-- A finite-mesh original law on simple quadratic roots has two stable
native-signal groups, with a fixed-power Lipschitz bound. -/
theorem finite_mesh_exact_root_partition (A : ℕ) :
    ∃ J C : ℕ, 1 ≤ C ∧
      ∀ K delta : ℝ, 2 ≤ K → 0 < delta → delta ≤ (K ^ J)⁻¹ →
        ∀ μ : Measure (EuclideanSpace ℝ (Fin 4)), IsProbabilityMeasure μ →
          RootBaseSmall μ → RootMeshCap μ K delta →
          ∀ P S : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
            (∀ᵐ p ∂μ, ‖erBase p‖ ≤ K ∧ eval (fun i => p i) P = 0 ∧
              K⁻¹ ≤ |eval (fun i => p i) (pderiv 3 P)| ∧
              |eval (fun i => p i) (pderiv 3 P)| ≤ K ∧ |eval (fun i => p i) S| ≤ K) →
            ∃ E : Fin 2 → Set (EuclideanSpace ℝ (Fin 4)),
              (∀ i, MeasurableSet (E i)) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
              μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧
              ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
                |eval (fun j => p j) S - eval (fun j => q j) S| ≤ K ^ C * ‖erBase p - erBase q‖ := by
  obtain ⟨J₀, N, hJ₀, hN, hcontrol⟩ := root_polynomial_control_from_mesh
  obtain ⟨J₁, c, hJ₁, hslab⟩ := root_slab_control_from_mesh A
  refine ⟨max J₀ J₁, N + c + 10, by omega, ?_⟩
  intro K delta hK hd hdJ μ hprob hbase hcap P S hP hS hgood
  haveI : IsProbabilityMeasure μ := hprob
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hd₀ : delta ≤ (K ^ J₀)⁻¹ := hdJ.trans
    (inv_anti₀ (pow_pos hK0 _) (pow_le_pow_right₀ hK1 (le_max_left _ _)))
  have hd₁ : delta ≤ (K ^ J₁)⁻¹ := hdJ.trans
    (inv_anti₀ (pow_pos hK0 _) (pow_le_pow_right₀ hK1 (le_max_right _ _)))
  exact exact_root_partition_of_controls N c A K P S μ hK hP hS
    (hcontrol K delta hK hd hd₀ μ hprob hbase hcap)
    (hslab K delta hK hd hd₁ μ hbase hcap) hgood

end

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
