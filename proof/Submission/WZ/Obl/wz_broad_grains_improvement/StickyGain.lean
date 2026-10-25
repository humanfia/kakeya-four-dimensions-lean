-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.StickyGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PhysicalDichotomy
import Submission.WZ.Obl.wz_sticky_katz_tao_every_scale
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry
import Submission.WZ.Obl.wz_balanced_tower_induction_transfer.Basic

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set
open WangZahlLot.Obl.wz_multiscale_finite_tower (VolumeBound)

set_option maxHeartbeats 1200000

/- The final sticky-volume combination follows the internal o005 split glue
(x0009/x0020), as exposed by x0689 in o198/x0628 at6e9f3d0,
O005/MainL.lean, Slab.lean and Comparison.lean. Here the hypothesis is our
EveryScaleAlternative, and the geometric slab and retained-cardinality lemmas
are imported from accepted o026/o099 rather than reproduced. -/

/-- The exact analytic input of the accepted sticky Katz--Tao theorem. -/
def FrostmanAllScales : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
    0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T d (x i) (v i) ⊆ I) →
    X d n x v → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T d (x i) (v i)) →
    O (d ^ η * n * d ^ 2) ≤ ∑ i, volume (Y i) →
    WangZahlLot.Obl.wz_sticky_katz_tao_every_scale.FEvery T d (d ^ (-η)) n x v →
    O (a * d ^ ε) ≤ volume (⋃ i, Y i)

/-- A positive exponent improvement, uniform for all admissible inputs. -/
def UniformGain (σ ω : ℝ) : Prop :=
  ∃ α κ η : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
    A d η (d ^ (-η)) (d ^ (-η)) n x v Y → VolumeBound σ ω κ α d n Y

/-- Testing the slab count on a perpendicular slab containing one input tube. -/
theorem slab_cardinality_lower {d η : ℝ} {n : ℕ} {x v : Fin n → V}
    (hd : 0 < d) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, T d (x i) (v i) ⊆ I) (hF : F d (d ^ (-η)) n x v) :
    d ^ η ≤ 8 * ((n : ℝ) * d) := by
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨u, hu, huv⟩ :=
    WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_unit_perp (hv i)
  let t := inner ℝ u (x i)
  have hcontains : T d (x i) (v i) ⊆ I ∩ Q u t d :=
    fun p hp => ⟨hball i hp,
      WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab hu huv (x i) d hp⟩
  have hcard : (1 : ℝ) ≤ ({j : Fin n | T d (x j) (v j) ⊆ I ∩ Q u t d}.ncard : ℝ) := by
    have hnonempty : Set.Nonempty {j : Fin n | T d (x j) (v j) ⊆ I ∩ Q u t d} :=
      ⟨i, hcontains⟩
    exact_mod_cast Nat.succ_le_of_lt hnonempty.ncard_pos
  have hreal : 1 ≤ (d ^ (-η) * (n : ℝ)) * (8 * d) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      O 1 ≤ O (q n {j | T d (x j) (v j) ⊆ I ∩ Q u t d}) :=
        ENNReal.ofReal_le_ofReal hcard
      _ ≤ O (d ^ (-η) * n) * volume (I ∩ Q u t d) := hF u t d hu hd
      _ ≤ O (d ^ (-η) * n) * O (8 * d) :=
        mul_le_mul_right
          (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hu t d hd.le) _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hcancel : d ^ η * d ^ (-η) = 1 := by
    rw [← Real.rpow_add hd, add_neg_cancel, Real.rpow_zero]
  calc
    d ^ η = d ^ η * 1 := (mul_one _).symm
    _ ≤ d ^ η * ((d ^ (-η) * (n : ℝ)) * (8 * d)) :=
      mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hd.le _)
    _ = (d ^ η * d ^ (-η)) * (8 * ((n : ℝ) * d)) := by ring
    _ = 8 * ((n : ℝ) * d) := by rw [hcancel, one_mul]

/-- Slab counting pays the cardinality factor in the sticky volume branch. -/
theorem gain_coefficient_le_sticky {σ ω α η b d : ℝ} {n : ℕ}
    (hσ : 0 ≤ σ) (hb : 0 ≤ b) (hd : 0 < d) (hd1 : d ≤ 1) (hn : 0 < n)
    (hα : α ≤ ω / 4) (hησ : η * σ ≤ ω / 4)
    (hcard : d ^ η ≤ 8 * ((n : ℝ) * d)) :
    (b * (8 : ℝ) ^ (-σ)) * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ) ≤
      b * d ^ (ω / 2) * (n * d ^ 2) := by
  have hnd : 0 < (n : ℝ) * d := mul_pos (Nat.cast_pos.mpr hn) hd
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hd η) hcard
    (neg_nonpos.mpr hσ)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hnd.le,
    ← Real.rpow_mul hd.le] at hpow
  calc
    (b * (8 : ℝ) ^ (-σ)) * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ) =
      b * d ^ (ω - α) * (n * d ^ 2) * ((8 : ℝ) ^ (-σ) * (n * d) ^ (-σ)) := by ring
    _ ≤ b * d ^ (ω - α) * (n * d ^ 2) * d ^ (η * -σ) := by gcongr
    _ = b * d ^ (ω - α + η * -σ) * (n * d ^ 2) := by
      rw [Real.rpow_add hd]; ring
    _ ≤ b * d ^ (ω / 2) * (n * d ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by nlinarith)) hb

/-- The multiscale dichotomy and the Frostman all-scales theorem give uniform gain. -/
theorem uniform_gain_of_every_scale {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hω : 0 < ω) (hFrostman : FrostmanAllScales) (hEvery : EveryScaleAlternative σ ω) :
    UniformGain σ ω := by
  have hT := WangZahlLot.wz_sticky_katz_tao_every_scale T rfl hFrostman
  obtain ⟨κ₁, hκ₁, η₁, hη₁, hS⟩ := hT (ω / 4) (by positivity)
  let θ := min η₁ (ω / 8)
  have hθ : 0 < θ := lt_min hη₁ (by positivity)
  have hθη₁ : θ ≤ η₁ := min_le_left _ _
  have hθω : θ ≤ ω / 8 := min_le_right _ _
  obtain ⟨α, hα, κ₂, hκ₂, η₂, hη₂, hAlt⟩ := hEvery θ hθ
  let η := min η₂ (ω / 8)
  have hη : 0 < η := lt_min hη₂ (by positivity)
  have hηη₂ : η ≤ η₂ := min_le_left _ _
  have hηω : η ≤ ω / 8 := min_le_right _ _
  let g := min α (ω / 4)
  have hg : 0 < g := lt_min hα (by positivity)
  have hgα : g ≤ α := min_le_left _ _
  have hgω : g ≤ ω / 4 := min_le_right _ _
  let κ := min κ₂ (κ₁ / 56 * (8 : ℝ) ^ (-σ))
  have hκ : 0 < κ := lt_min hκ₂ (by positivity)
  refine ⟨g, κ, η, hg, hκ, hη, ?_⟩
  intro d hd hd100 n x v Y hA
  have hd1 : d ≤ 1 := hd100.trans (by norm_num)
  have hcard := slab_cardinality_lower hd hA.1 (fun i => (hA.2.1 i).1)
    (fun i => (hA.2.1 i).2.1) hA.2.2.2.2.2
  have hA₂ := admissible_mono hd hd1 hηη₂ hA
  rcases hAlt d hd hd100 n x v Y hA₂ with hGain | ⟨m, x', v', Y', M', L', hA', hU, hret, hkt⟩
  · exact (show VolumeBound σ ω κ₂ α d n Y from hGain).mono
      hd hd1 hκ.le (min_le_left _ _) hgα
  have hkt' := WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy.KatzTaoEveryScale.mono
    hkt hd hd1 hθη₁
  have hA'₁ := hA'.mono hd hd1 hθη₁ le_rfl le_rfl
  have hS' := hS d hd hd100 m x' v' Y' hA'₁.1
    (fun j => (hA'₁.2.1 j).1) (fun j => (hA'₁.2.1 j).2.1) hA'₁.2.2.1
    (fun j => (hA'₁.2.1 j).2.2.1) (fun j => (hA'₁.2.1 j).2.2.2) hA'₁.2.2.2.1 hkt'
  have hcount₀ := WangZahlLot.Obl.wz_balanced_tower_induction_transfer.retained_cardinality
    hd hd1 hA hA' hret
  have hcount : d ^ (η + θ) * (n : ℝ) ≤ 56 * (m : ℝ) := by
    rw [add_comm θ η] at hcount₀
    linarith
  have hpow : d ^ (ω / 2) ≤ d ^ (ω / 4) * d ^ (η + θ) := by
    rw [← Real.rpow_add hd]
    exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hsticky : O (κ₁ / 56 * d ^ (ω / 2) * (n * d ^ 2)) ≤ volume (⋃ i, Y i) := by
    calc
      O (κ₁ / 56 * d ^ (ω / 2) * (n * d ^ 2)) ≤
          O (κ₁ * d ^ (ω / 4) * (m * d ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          κ₁ / 56 * d ^ (ω / 2) * (n * d ^ 2) ≤
              κ₁ / 56 * (d ^ (ω / 4) * d ^ (η + θ)) * (n * d ^ 2) := by gcongr
          _ = κ₁ / 56 * d ^ (ω / 4) * (d ^ (η + θ) * n) * d ^ 2 := by ring
          _ ≤ κ₁ / 56 * d ^ (ω / 4) * (56 * m) * d ^ 2 := by gcongr
          _ = κ₁ * d ^ (ω / 4) * (m * d ^ 2) := by ring
      _ ≤ volume (⋃ j, Y' j) := hS'
      _ ≤ volume (⋃ i, Y i) := measure_mono hU
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hsticky
  apply le_trans ?_ (gain_coefficient_le_sticky hσ (by positivity) hd hd1 hA.1
    hgω (by nlinarith) hcard)
  gcongr
  exact min_le_right _ _

/-- A uniform gain supplies the first branch of the frozen grains improvement. -/
theorem improvement_of_uniform_gain {σ ω ζ ε : ℝ}
    (hε : 0 < ε) (hGain : UniformGain σ ω) : L σ ω ζ ε := by
  obtain ⟨α, κ, η, hα, hκ, hη, HG⟩ := hGain
  refine ⟨α, κ, min η ε, 1 / 100, hα, hκ, lt_min hη hε, min_le_right _ _,
    by norm_num, le_rfl, ?_⟩
  intro d hd hdd n x v Y hA ρ c hD
  exact Or.inl (HG d hd hdd n x v Y
    (admissible_mono hd (hdd.trans (by norm_num)) (min_le_left _ _) hA))

end WangZahlLot.Obl.wz_broad_grains_improvement
