-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupedCertificate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.ScaleClasses
import Submission.WZ.Obl.wz_multiscale_finite_tower.CertificateRetention

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced)

theorem insert_grouped_certificate {J k : ℕ} {d θ ζ ε g gap gap' r K L F : ℝ}
    (C : HierarchyCertificate d θ g gap J) (hk : k < J)
    (G : GroupedSelection (C.tree.parent k) (d ^ (θ + 2 * ζ)) (d ^ (-ζ)))
    (Q : GroupedGeometry C.tree G d r K L F)
    (hd : 0 < d) (hd1 : d < 1) (hθ : 0 ≤ θ) (hζ : 0 < ζ)
    (hε : 6 * θ + 5 * ζ ≤ ε) (hgap : gap' ≤ gap)
    (q : ℕ) (hq : 0 < q) (hn : ((C.tree.layer J).card : ℝ) < (d ^ (-ζ)) ^ q)
    (hsmall : (q : ℝ) ^ (J + 2) * d ^ ζ ≤ 1)
    (hparents : d ^ ζ * (C.tree.layer J).card ≤
      (Finset.univ.filter (fun i => C.tree.ancestor k i ∈ G.parents)).card)
    (hr : 0 < r) (hr64 : r ≤ (C.tree.layer k).radius / 64)
    (hsr : (C.tree.layer (k + 1)).radius < r)
    (hlo₁ : d ^ g * (C.tree.layer k).radius ≤ r)
    (hlo₂ : d ^ g * r ≤ (C.tree.layer (k + 1)).radius)
    (hhi₁ : r ≤ d ^ gap' * (C.tree.layer k).radius)
    (hhi₂ : (C.tree.layer (k + 1)).radius ≤ d ^ gap' * r)
    (hK : K ≤ d ^ (-ε)) (hF : F ≤ d ^ (-ε)) (hL : 0 ≤ L)
    (hslab : L * d ^ (-(5 * θ + 6 * ζ)) ≤ d ^ (-ε))
    (hmass : 56 * d ^ ε ≤ d ^ (3 * θ + 4 * ζ)) :
    ∃ C' : HierarchyCertificate d ε g gap' (J + 1),
      (∀ j, (C'.tree.layer j).radius =
        if j ≤ k then (C.tree.layer j).radius else if j = k + 1 then r else (C.tree.layer (j - 1)).radius) ∧
      (C'.tree.layer (J + 1)).card ≤ (C.tree.layer J).card ∧
      (⋃ i, C'.shading i) ⊆ (⋃ i, C.shading i) ∧
      ENNReal.ofReal (d ^ ε) * (∑ i, volume (C.shading i)) ≤ ∑ i, volume (C'.shading i) := by
  classical
  let U := Finset.univ.filter (fun i => C.tree.ancestor (k + 1) i ∈ G.selected)
  let ell : ℝ := 2 * θ + 4 * ζ
  let τ : ℝ := θ + ζ
  have hraw : d ^ (2 * θ + 3 * ζ) * (C.tree.layer J).card ≤ U.card := by
    have hh := G.leaf_retention hk (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hd _)
      (Real.rpow_nonneg hd.le _) (C.control.balanced (k + 1) (by omega)) hparents
    have he : d ^ (θ + 2 * ζ) * d ^ ζ / d ^ (-θ) = d ^ (2 * θ + 3 * ζ) := by
      rw [← Real.rpow_add hd, ← Real.rpow_sub hd]
      congr 1
      ring
    simpa only [he] using hh
  have hU : U.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos (Real.rpow_pos_of_pos hd _) (Nat.cast_pos.mpr (C.tree.layer J).card_pos)).trans_le hraw))
  have hR' : 1 < d ^ (-ζ) := by
    rw [Real.rpow_neg hd.le]
    exact (one_lt_inv₀ (Real.rpow_pos_of_pos hd ζ)).mpr (Real.rpow_lt_one hd.le hd1 hζ)
  obtain ⟨S, hSU, hS, hcardreg, hbalraw, hbalmid, hclosed⟩ :=
    G.regularize hk C.control.balanced q hq hR' hn hU
  have hSsel (i) (hi : i ∈ S) : C.tree.ancestor (k + 1) i ∈ G.selected :=
    (Finset.mem_filter.mp (hSU hi)).2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqsmall : d ^ ζ * (q : ℝ) ^ (k + 2) ≤ 1 := by
    calc
      _ ≤ d ^ ζ * (q : ℝ) ^ (J + 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (by omega)) (Real.rpow_nonneg hd.le _)
      _ ≤ 1 := by simpa only [mul_comm] using hsmall
  have hretain : d ^ ell * (C.tree.layer J).card ≤ S.card := by
    have he : d ^ ell = d ^ ζ * d ^ (2 * θ + 3 * ζ) := by
      rw [← Real.rpow_add hd]
      congr 1
      dsimp [ell]
      ring
    calc
      _ = d ^ ζ * (d ^ (2 * θ + 3 * ζ) * (C.tree.layer J).card) := by rw [he, mul_assoc]
      _ ≤ d ^ ζ * U.card := mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hd.le _)
      _ ≤ d ^ ζ * ((q : ℝ) ^ (k + 2) * S.card) :=
        mul_le_mul_of_nonneg_left hcardreg (Real.rpow_nonneg hd.le _)
      _ ≤ S.card := by
        rw [← mul_assoc]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hqsmall (Nat.cast_nonneg S.card)
  have hmax : max (d ^ (-θ)) (d ^ (-ζ)) ≤ d ^ (-τ) := max_le
    (Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by dsimp [τ]; linarith))
    (Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by dsimp [τ]; linarith))
  have hbal (j) (hj : j ≤ J) : Balanced S (C.tree.ancestor j) (d ^ (-τ)) :=
    balanced_mono (hbalraw j hj) hmax
  let R := Classical.choice (exists_hierarchy_restriction C.tree S hS)
  have H₀ := R.control_of_power_retention C.control hd hd1.le (show θ ≤ ε by linarith)
    (show τ ≤ ε by dsimp [τ]; linarith) (show 3 * θ + τ + ell ≤ ε by dsimp [τ, ell]; linarith) hbal hretain
  have H' := H₀.weaken_gap hd hd1.le hgap
  have hden (i) (hi : i ∈ S) : ENNReal.ofReal (d ^ ε * d ^ 2) ≤ volume (C.shading i) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith : θ ≤ ε)) (sq_nonneg d))).trans (C.family.density i)
  let C₀ : HierarchyCertificate d ε g gap' J := ⟨R.tree, C.shading ∘ R.map J, C.root_axis, C.scalar,
    H', R.alignment C.alignment,
    R.aligned_family C hd hd1.le (by linarith) (by dsimp [ell]; linarith) hretain C.shading
      (fun i _ => C.family.measurable i) (fun _ _ => Subset.rfl) hden⟩
  let I := Classical.choice (exists_restricted_grouping G hk R hSsel hclosed r)
  have hslab' (t : Fin (R.tree.layer k).card) :
      L * {i | i ∈ G.selected ∧ G.group i = i ∧ C.tree.parent k i = R.map k t}.ncard ≤
        d ^ (-ε) * {i | I.upper i = t}.ncard := by
    have hh := I.coarse_retention hk (Real.rpow_pos_of_pos hd _) (Real.rpow_nonneg hd.le _)
      (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _) C.control.balanced hSsel (hbal k hk.le) hretain t
    apply slab_coefficient_of_retention (Real.rpow_pos_of_pos hd _) hL (Nat.cast_nonneg _) hh
    have he : (d ^ (-θ) * d ^ (-τ) * (d ^ (-ζ) * d ^ (-θ))) / d ^ ell = d ^ (-(5 * θ + 6 * ζ)) := by
      rw [← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_sub hd]
      congr 1
      dsimp [τ, ell]
      ring
    simpa only [mul_div_assoc, he] using hslab
  have Hupper := I.upper_control C.control Q hk hd hr hr64 hlo₁ hhi₁ hK hslab'
  have Hlower := I.lower_control C.control Q hk hd hd1.le (show θ ≤ ε by linarith)
    hr hsr hlo₂ hhi₂ hF
  have hmid : Balanced Finset.univ (I.lower ∘ R.tree.ancestor (k + 1)) (d ^ (-ε)) :=
    balanced_mono (I.balanced hbalmid)
      (Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith : -ε ≤ -ζ))
  have hM (i) : ‖I.middle.direction i - C₀.root_axis‖ ≤ 1 / 10 ∧
      inner ℝ (I.middle.direction i) (axisMidpoint (I.middle.position i) (I.middle.direction i)) = C₀.scalar ∧
      ‖axisMidpoint (I.middle.position i) (I.middle.direction i)‖ ≤ 7 / 8 := by
    simpa only [I.position, I.direction] using
      And.intro (C.alignment.direction_cap (k + 1) (by omega) (by omega) (I.map i))
        ⟨C.alignment.aligned (k + 1) (by omega) (by omega) (I.map i),
          C.alignment.midpoint (k + 1) (by omega) (by omega) (I.map i)⟩
  let C' := insertCertificate C₀ hk I.middle I.lower I.lower_surjective I.upper I.commute Hupper Hlower hmid hM
  let E := afterLayerEquiv k I.middle R.tree.layer (J + 1) J (by omega) (by omega)
  have hcard' : (C'.tree.layer (J + 1)).card = (R.tree.layer J).card := by
    change (insertedLayer k I.middle R.tree.layer (J + 1)).card = _
    simpa only [Fintype.card_fin] using Fintype.card_congr E.index
  have hsum : (∑ i, volume (C'.shading i)) = ∑ i ∈ S, volume (C.shading i) := by
    change (∑ i, volume (C.shading (R.map J (E.index i)))) = _
    exact (Equiv.sum_comp E.index (fun i => volume (C.shading (R.map J i)))).trans
      (R.sum_bottom (fun i => volume (C.shading i)))
  refine ⟨C', ?_, ?_, ?_, ?_⟩
  · intro j
    change (insertedLayer k I.middle R.tree.layer j).radius = _
    unfold insertedLayer
    split_ifs <;> simp only [R.radius, I.radius]
  · rw [hcard', R.bottom_card]
    exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin _)
  · change (⋃ i, C.shading (R.map J (E.index i))) ⊆ _
    exact iUnion_subset fun i => subset_iUnion C.shading (R.map J (E.index i))
  · rw [hsum]
    apply C.family.mass_retention_of_card hd hd1.le S hretain
    convert hmass using 1
    congr 1
    dsimp [ell]
    ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
