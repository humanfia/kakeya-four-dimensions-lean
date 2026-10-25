-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SaturatedBodyEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SaturatedBodyEstimate.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PackedEstimate
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismBodyNormalization
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyEstimate BodyConvexCount BodyPacking)

noncomputable section

/-- The packed body estimate in a saturated prism, transported back to the
original coordinates. All analytic constants are uniform in its widths. -/
theorem saturated_prism_body_estimate {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (n : ℕ) (U Y : Fin n → Set V) (x : Fin n → V) (a b r w m p C : ℝ),
      0 < n → (n : ℝ) ≤ d ^ (-100 : ℝ) →
      0 < a → a ≤ b → b ≤ 4 → 0 < r → d ≤ r / 4 → 0 < w →
      d ≤ Real.sqrt (w / (4 * a * b)) / 16 → 1 ≤ m → 1 ≤ p → 0 < C →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) →
      (∀ i, ball (x i) r ⊆ U i) →
      (∀ i, ∃ q ∈ U i, ∃ q' ∈ U i, (1 / 4 : ℝ) ≤ dist q q') →
      (∀ i, μ (U i) = O w) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, O (d ^ η) * μ (U i) ≤ μ (Y i)) →
      BodyConvexCount U w m → BodyPacking U w p →
      m * (4 * a * b) ≤ C * n * w →
      ∀ z e, (∀ i, U i ⊆ P a b 4 z e) →
      O ((4 * a * b) * (A / C) * d ^ ε * (Real.sqrt (w / (4 * a * b)) / 16) ^ ω *
        m ^ (σ / 2) * p ^ (-σ) * (w / (4 * a * b)) ^ (σ / 2)) ≤ μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hsmall, H⟩ := packed_convex_body_estimate hbody ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hsmall, ?_⟩
  intro d hd hdd n U Y x a b r w m p C hn hnmax ha hab hb hr hdr hw hdB hm hp hC
    hcompact hconvex hball hlong hvolume hYm hYU hden hcount hpack hsat z e hbox
  have hbpos : 0 < b := ha.trans_le hab
  have hJ : 0 < 1 / (4 * a * b) := by positivity
  have hww : 0 < w / (4 * a * b) := by positivity
  obtain ⟨f, hvol, hunit, hgeom⟩ :=
    prism_body_normalization ha hab hb hr hdr hw U x hcompact hconvex hball hlong hvolume z e hbox
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
    (Real.sqrt (w / (4 * a * b)) / 16) (w / (4 * a * b)) m p
    hn hnmax hdB hww hm hp hgeom hunit
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono (hYU i)) hdensity hK hP
  have hsat' : m * 1 ≤ C * n * (w / (4 * a * b)) := by
    rw [mul_one, ← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 4 * a * b)]
    exact hsat
  have hscalar := saturated_packed_body_scalar (σ := σ) (ω := ω) (ε := ε) hA.le hd.le
    (by positivity : 0 ≤ Real.sqrt (w / (4 * a * b)) / 16)
    (zero_lt_one.trans_le hm) (zero_lt_one.trans_le hp) hww hC hsat'
  simp only [mul_one] at hscalar
  have hlow := (ENNReal.ofReal_le_ofReal hscalar).trans hbound
  have hjoin : μ (⋃ i, f '' Y i) = O (1 / (4 * a * b)) * μ (⋃ i, Y i) := by
    rw [← image_iUnion]
    exact hvol _
  have hinv : O (4 * a * b) * O (1 / (4 * a * b)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * a * b)]
    have he : (4 * a * b) * (1 / (4 * a * b)) = 1 := by field_simp
    rw [he, ENNReal.ofReal_one]
  calc
    _ = O (4 * a * b) * O ((A / C) * d ^ ε * (Real.sqrt (w / (4 * a * b)) / 16) ^ ω *
        m ^ (σ / 2) * p ^ (-σ) * (w / (4 * a * b)) ^ (σ / 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * a * b)]
      congr 1
      ring
    _ ≤ O (4 * a * b) * μ (⋃ i, f '' Y i) := mul_le_mul' le_rfl hlow
    _ = μ (⋃ i, Y i) := by rw [hjoin, ← mul_assoc, hinv, one_mul]

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
