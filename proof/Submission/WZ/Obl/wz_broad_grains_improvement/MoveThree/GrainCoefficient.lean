-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainCoefficient.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainCoefficient.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LocalCoefficient
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.StateSelection
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (count Upper)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume)

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The expanded-plate neighborhood appearing in the frozen local count. -/
def grainNear {L : ℕ} (a ρ c : ℝ) (z : Fin L → V)
    (e : Fin L → V ≃ₗᵢ[ℝ] V) (j j' : Fin L) : Prop :=
  P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j)

def grainCoefficient {L : ℕ} (a ρ c : ℝ) (z : Fin L → V)
    (e : Fin L → V ≃ₗᵢ[ℝ] V) (Q : Finset (Fin L)) : ℝ :=
  localCoefficient (fun j => P a (ρ * c) c (z j) (e j))
    (a * (ρ * c) * c) (grainNear a ρ c z e) Q

theorem grainCoefficient_bounds {L : ℕ} {a ρ c : ℝ}
    (ha : 0 ≤ a) (hrc : 0 ≤ ρ * c) (hc : 0 ≤ c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (Q : Finset (Fin L)) :
    1 ≤ grainCoefficient a ρ c z e Q ∧
      grainCoefficient a ρ c z e Q ≤ max 1 (Q.card : ℝ) := by
  refine ⟨one_le_localCoefficient _ _ _ _, ?_⟩
  apply localCoefficient_le_card _ _ _ (by positivity)
  intro j _
  exact (frozen_prism_volume ha hrc hc (z j) (e j)).ge

theorem grainCoefficient_count {L : ℕ} {a ρ c : ℝ}
    (ha : 0 ≤ a) (hrc : 0 ≤ ρ * c) (hc : 0 ≤ c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (Q : Finset (Fin L)) :
    ∀ j ∈ Q, ∀ W, Convex ℝ W →
      O (q L {j' | j' ∈ Q ∧
        P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤
      O (grainCoefficient a ρ c z e Q) * μ W := by
  intro j hj W hW
  have hh := localCoefficient_upper (fun j => P a (ρ * c) c (z j) (e j))
    (grainNear a ρ c z e) Q (by positivity : 0 ≤ a * (ρ * c) * c)
    (fun j _ => (frozen_prism_volume ha hrc hc (z j) (e j)).ge) j hj W hW
  have hset :
      {j' | j' ∈ Q ∧ grainNear a ρ c z e j j' ∧ P a (ρ * c) c (z j') (e j') ⊆ W} =
      (↑((Q.filter (grainNear a ρ c z e j)).filter
        (fun j' => P a (ρ * c) c (z j') (e j') ⊆ W)) : Set (Fin L)) := by
    ext j'
    simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, and_assoc]
  change O (q L {j' | j' ∈ Q ∧ grainNear a ρ c z e j j' ∧
    P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ _
  simpa only [q, hset, Set.ncard_coe_finset, count, grainCoefficient] using hh

/-- The finite local coefficient supplies exactly the count hypothesis needed
to close Move 3's same-scale alternative. Its positivity is automatic. -/
theorem stage_three_of_small_grainCoefficient {ω ζ δ h h' ρ a c g t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hρlow : δ ^ (1 - ω / 100) ≤ ρ)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (hlen : δ ^ ζ * (ρ / δ) * N / n ≤ c) (hρup : ρ ≤ δ ^ (ω / 100))
    (Q : Finset (Fin L)) (hsmall : grainCoefficient a ρ c z e Q ≤ δ ^ (-ζ))
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j))
    (hbudget : O (δ ^ h') ≤ O (t / 2) * O (δ ^ h)) :
    J ω ζ δ h' ρ c n x v Y 3 := by
  have ha : 0 ≤ a := hδ.le.trans hG.1
  have hrc : 0 ≤ ρ * c := ha.trans hG.2.1
  have hc : 0 ≤ c := hrc.trans hG.2.2.1
  have hpos : 0 < grainCoefficient a ρ c z e Q :=
    zero_lt_one.trans_le (grainCoefficient_bounds ha hrc hc z e Q).1
  have hbudget' : O (δ ^ h') ≤ O t * O (δ ^ h) :=
    hbudget.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)
  exact stage_three_of_grain_selection hδ hδ1 hh ht hC hρlow hB hG hlen hρup Q
    hpos hsmall hretain hbudget (grain_selection_density hδ hG Q hretain hbudget')
    (grainCoefficient_count ha hrc hc z e Q)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
