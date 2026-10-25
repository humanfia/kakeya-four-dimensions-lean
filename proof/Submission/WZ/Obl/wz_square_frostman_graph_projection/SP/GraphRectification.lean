-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphRectification.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphRectificationHighDegree

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Restricting the right vertices cannot increase the number of paths. -/
theorem graph_three_paths_restrict {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (T : Finset J) (x : I) (b : T) :
    ((graphThreePaths (fun i (j : T) => R i j) x b).card : ℝ) ≤
      ((graphThreePaths R x (b : J)).card : ℝ) := by
  classical
  let φ (p : I × T) : I × J := (p.1, p.2)
  have hmap : ∀ p ∈ graphThreePaths (fun i (j : T) => R i j) x b,
      φ p ∈ graphThreePaths R x (b : J) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  have hinj : Set.InjOn φ (↑(graphThreePaths (fun i (j : T) => R i j) x b) : Set (I × T)) := by
    intro p hp q hq hpq
    apply Prod.ext
    · exact congrArg (fun p : I × J => p.1) hpq
    · exact Subtype.ext (congrArg (fun p : I × J => p.2) hpq)
  exact_mod_cast Finset.card_le_card_of_injOn φ hmap hinj

/-- A dense finite bipartite graph has large vertex subsets between which
every pair is joined by polynomially many paths of length three. -/
theorem graph_rectification {I J : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Nonempty J] (R : I → J → Prop) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hdensity : d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ)) :
    ∃ (X : Finset I) (Y : Finset J), X.Nonempty ∧ Y.Nonempty ∧
      (d / 4) * (Fintype.card I : ℝ) ≤ (X.card : ℝ) ∧
      (d ^ 2 / 16) * (Fintype.card J : ℝ) ≤ (Y.card : ℝ) ∧
      ∀ x ∈ X, ∀ b ∈ Y,
        (d ^ 7 / 524288) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
          ((graphThreePaths R x b).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  let f (j : J) : ℝ := (Finset.univ.filter (fun i => R i j)).card
  have hf (j : J) : 0 ≤ f j ∧ f j ≤ (Fintype.card I : ℝ) := by
    constructor
    · exact Nat.cast_nonneg _
    · dsimp [f]
      exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset I) _).trans_eq Finset.card_univ
  have hsum : d * (Fintype.card I : ℝ) * ((Finset.univ : Finset J).card : ℝ) ≤ ∑ j : J, f j := by
    have hs := sum_relation_degree R
    simp only [Finset.card_univ]
    dsimp [f]
    rw [hs]
    exact hdensity
  obtain ⟨T, hTuniv, hTsize, hTcol⟩ := finite_many_large_values (Finset.univ : Finset J) f hN hd.le
    (fun j _ => hf j) hsum
  simp only [Finset.card_univ] at hTsize
  have hT : T.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < T.card := (mul_pos (by positivity : 0 < d / 2) hM).trans_le hTsize
    exact_mod_cast hh
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  let R' (i : I) (j : T) : Prop := R i (j : J)
  have hcols (j : T) : (d / 2) * (Fintype.card I : ℝ) ≤
      ((Finset.univ.filter (fun i => R' i j)).card : ℝ) := hTcol j j.2
  obtain ⟨X, Y₀, hX, hY₀, hXsize, hY₀size, hpaths⟩ :=
    graph_rectification_high_degree R' (by positivity : 0 < d / 2) (by linarith) hcols
  let Y := Y₀.image (fun j : T => (j : J))
  have hYcard : Y.card = Y₀.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hY : Y.Nonempty := hY₀.image _
  simp only [Fintype.card_coe] at hY₀size hpaths
  refine ⟨X, Y, hX, hY, ?_, ?_, ?_⟩
  · convert hXsize using 1 <;> ring
  · rw [hYcard]
    calc
      (d ^ 2 / 16) * (Fintype.card J : ℝ) = ((d / 2) / 4) * ((d / 2) * (Fintype.card J : ℝ)) := by ring
      _ ≤ ((d / 2) / 4) * (T.card : ℝ) := by gcongr
      _ ≤ _ := hY₀size
  · intro x hx b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    have hp := (hpaths x hx b₀ hb₀).trans (graph_three_paths_restrict R T x b₀)
    apply le_trans _ hp
    calc
      (d ^ 7 / 524288) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) =
          ((d / 2) ^ 6 / 4096) * (Fintype.card I : ℝ) * ((d / 2) * (Fintype.card J : ℝ)) := by ring
      _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
