import Submission.Obl.k4_narrow_projected_row_parents.Front
import Submission.Obl.k4_known_atlas_normalization_composition.Transfer

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Take a subsequence of all the original data simultaneously. -/
def Model.reindex (cfg : Model α) (φ : ℕ → ℕ) : Model α :=
  ⟨cfg.N ∘ φ, cfg.K ∘ φ, cfg.d, cfg.κ, cfg.ℓ, cfg.S, cfg.U, cfg.e₀,
    cfg.ν ∘ φ, cfg.μ ∘ φ, cfg.ρ ∘ φ, cfg.π ∘ φ, cfg.b ∘ φ, cfg.P ∘ φ,
    cfg.T ∘ φ, cfg.n ∘ φ, fun k => cfg.j (φ k), fun k => cfg.A (φ k),
    fun k => cfg.B (φ k), fun k => cfg.c (φ k), fun k => cfg.F (φ k)⟩

theorem Model.Valid.reindex {cfg : Model α} (hv : Model.Valid cfg) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) : Model.Valid (cfg.reindex φ) := by
  refine ⟨fun k => hv.scale (φ k), hv.scale_limit.comp hφ,
    ⟨fun k => hv.subpower.1 (φ k), fun ε hε => hφ.eventually (hv.subpower.2 ε hε)⟩,
    hv.dimension_nonneg, hv.dimension_lt_one, hv.rate_pos, hv.rate_le_one,
    hv.transverse_pos, hv.palette_pos, hv.palette_le_one, hv.depth_pos, hv.defect_pos,
    fun k => hv.basic (φ k), ?_, ?_, ?_⟩
  · intro R hR
    exact hφ.eventually (hv.caps R hR)
  · intro R hR
    exact hφ.eventually (hv.atlas R hR)
  · intro R hR
    exact hφ.eventually (hv.nested R hR)

/-- A subpower loss on a subsequence extends by one to the original sequence. -/
theorem subpow_extend {N M : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hN : ∀ k, 1 ≤ N k) (hM : Model.Subpow (N ∘ φ) M) :
    Model.Subpow N (Function.extend φ M (fun _ => 1)) := by
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hM ε hε)
  filter_upwards [eventually_ge_atTop (φ j₀)] with k hk
  by_cases hm : ∃ j, φ j = k
  · obtain ⟨j, rfl⟩ := hm
    rw [hφ.injective.extend_apply]
    exact hj₀ j (hφ.le_iff_le.mp hk)
  · rw [Function.extend_apply' M (fun _ => 1) k hm]
    exact Real.one_le_rpow (hN k) hε.le

/-- Candidates on a subsequence are candidates for the original model. -/
theorem candidates_of_reindex {cfg : Model α} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (h : (cfg.reindex φ).Candidates) : cfg.Candidates := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, fun ε hε => ?_⟩
  exact Submission.Obl.k4_known_atlas_normalization_composition.frequently_of_subsequence
    hφ (hc ε hε)

/-- Row parents with a subpower loss return from every strictly increasing
subsequence. Their original assignment weights remain unchanged. -/
theorem rowParents_of_reindex {cfg : Model α} {φ : ℕ → ℕ}
    (hN : ∀ k, 1 ≤ cfg.N k) (hφ : StrictMono φ) {r : ℝ}
    (h : RowParents (cfg.reindex φ) r) : RowParents cfg r := by
  obtain ⟨e, he, M, hM, hMsub, hfreq⟩ := h
  let M' : ℕ → ℝ := Function.extend φ M (fun _ => 1)
  have hM' : ∀ k, 1 ≤ M' k := by
    intro k
    by_cases hm : ∃ j, φ j = k
    · obtain ⟨j, rfl⟩ := hm
      simpa only [M', hφ.injective.extend_apply] using hM j
    · change 1 ≤ Function.extend φ M (fun _ => 1) k
      rw [Function.extend_apply' M (fun _ => 1) k hm]
  refine ⟨e, he, M', hM', subpow_extend hφ hN hMsub, ?_⟩
  apply Submission.Obl.k4_known_atlas_normalization_composition.frequently_of_subsequence
    hφ.tendsto_atTop
  apply hfreq.mono
  rintro k ⟨RP⟩
  have heq : M' (φ k) = M k := hφ.injective.extend_apply _ _ _
  rw [heq]
  exact ⟨{
    Q := RP.Q
    B := RP.B
    lam := RP.lam
    G := RP.G
    measurable_G := RP.measurable_G
    G_sub := RP.G_sub
    mass := RP.mass
    B_le := RP.B_le
    lam_le := RP.lam_le
    row := RP.row }⟩

end

end Submission.Obl.k4_narrow_projected_row_parents
