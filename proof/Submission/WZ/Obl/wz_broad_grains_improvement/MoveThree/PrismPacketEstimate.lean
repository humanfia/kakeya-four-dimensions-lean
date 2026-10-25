-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismPacketEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismPacketEstimate.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SharpBodyEstimate
import Submission.WZ.Obl.wz_terminal_grains_restoration.Basic

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate BodyConvexCount BodyPacking)

noncomputable section

/-- The sharp body estimate before saturation. Its dependence on the number
of bodies is linear, so it can be summed over angular packets. -/
theorem sharp_prism_packet_estimate {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (n : ℕ) (U Y : Fin n → Set V) (x : Fin n → V) (a b r w m p : ℝ),
      0 < n → (n : ℝ) ≤ d ^ (-100 : ℝ) →
      0 < a → a ≤ b → b ≤ 4 → 0 < r → d ≤ r / 4 → 0 < w →
      d ≤ r / (8192 * a) → 1 ≤ m → 1 ≤ p →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) →
      (∀ i, ball (x i) r ⊆ U i) →
      (∀ i, ∃ q ∈ U i, ∃ q' ∈ U i, (1 / 4 : ℝ) ≤ dist q q') →
      (∀ i, μ (U i) = O w) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, O (d ^ η) * μ (U i) ≤ μ (Y i)) →
      BodyConvexCount U w m → BodyPacking U w p →
      ∀ z e, (∀ i, U i ⊆ P a b 4 z e) →
      O (A * d ^ ε * (r / (8192 * a)) ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) *
        (w / (4 * a * b)) ^ (σ / 2) * w * n) ≤ μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hsmall, H⟩ := packed_convex_body_estimate hbody ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hsmall, ?_⟩
  intro d hd hdd n U Y x a b r w m p hn hnmax ha hab hb hr hdr hw hdB hm hp
    hcompact hconvex hball hlong hvolume hYm hYU hden hcount hpack z e hbox
  have hbpos : 0 < b := ha.trans_le hab
  have hJ : 0 < 1 / (4 * a * b) := by positivity
  have hww : 0 < w / (4 * a * b) := by positivity
  obtain ⟨f, hvol, hunit, hgeom⟩ :=
    sharp_prism_body_normalization ha hab hb hr hdr hw U x hcompact hconvex hball hlong hvolume z e hbox
  have heq : 1 / (4 * a * b) * w = w / (4 * a * b) := by ring
  have hK : BodyConvexCount (fun i => f '' U i) (w / (4 * a * b)) m := by
    simpa only [heq] using hcount.affine_image hw.le hJ f hvol
  have hP : BodyPacking (fun i => f '' U i) (w / (4 * a * b)) p := by
    simpa only [heq] using hpack.affine_image hw.le hJ f hvol
  have hdensity i : O (d ^ η) * μ (f '' U i) ≤ μ (f '' Y i) := by
    rw [hvol, hvol]
    calc
      _ = O (1 / (4 * a * b)) * (O (d ^ η) * μ (U i)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl (hden i)
  have hbound := H d hd hdd n (fun i => f '' U i) (fun i => f '' Y i) (fun i => f (x i))
    (r / (8192 * a)) (w / (4 * a * b)) m p
    hn hnmax hdB hww hm hp hgeom hunit
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono (hYU i)) hdensity hK hP
  have hjoin : μ (⋃ i, f '' Y i) = O (1 / (4 * a * b)) * μ (⋃ i, Y i) := by
    rw [← image_iUnion]
    exact hvol _
  have hinv : O (4 * a * b) * O (1 / (4 * a * b)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * a * b)]
    have he : (4 * a * b) * (1 / (4 * a * b)) = 1 := by field_simp
    rw [he, ENNReal.ofReal_one]
  calc
    _ = O (4 * a * b) * O (A * d ^ ε * (r / (8192 * a)) ^ ω *
        m ^ (-1 + σ / 2) * p ^ (-σ) * n * (w / (4 * a * b)) ^ (1 + σ / 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * a * b),
        Real.rpow_add hww, Real.rpow_one]
      congr 1
      field_simp
    _ ≤ O (4 * a * b) * μ (⋃ i, f '' Y i) := mul_le_mul' le_rfl hbound
    _ = μ (⋃ i, Y i) := by rw [hjoin, ← mul_assoc, hinv, one_mul]

/-- A linear estimate on packet unions can be summed with any real
pointwise overlap bound, including angular overlap powers. -/
theorem packet_union_linear_lower {ι : Type*} [Fintype ι] (Y : ι → Set V)
    (hYm : ∀ i, MeasurableSet (Y i)) {A M : ℝ} {N : ι → ℝ}
    (hA : 0 ≤ A) (hN : ∀ i, 0 ≤ N i)
    (hlow : ∀ i, O (A * N i) ≤ μ (Y i))
    (hover : ∀ p ∈ ⋃ i, Y i, ((Finset.univ.filter fun i => p ∈ Y i).card : ℝ) ≤ M) :
    O (A * ∑ i, N i) ≤ O M * μ (⋃ i, Y i) := by
  classical
  calc
    _ = ∑ i, O (A * N i) := by
      change ENNReal.ofReal (A * ∑ i, N i) = ∑ i, ENNReal.ofReal (A * N i)
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hA (hN i))]
    _ ≤ ∑ i, μ (Y i) := Finset.sum_le_sum (fun i _ => hlow i)
    _ ≤ O M * μ (⋃ i, Y i) := by
      have hh := WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_le_of_mult_le
        volume Finset.univ Y (fun i _ => hYm i) M
        (by simpa only [Finset.mem_univ, iUnion_true,
          WangZahlLot.Obl.wz_terminal_grains_restoration.mult] using hover)
      simpa only [Finset.mem_univ, iUnion_true] using hh

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
