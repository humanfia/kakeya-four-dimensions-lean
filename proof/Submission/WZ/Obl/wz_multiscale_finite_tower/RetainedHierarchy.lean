-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.RetainedHierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.BadGaps

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

def RetainedHierarchy (d ε g gap : ℝ) (B n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ∃ J : ℕ, ∃ C : HierarchyCertificate d ε g gap J, J ≤ B ∧ (C.tree.layer J).card ≤ n ∧
    (⋃ i, C.shading i) ⊆ (⋃ i, Y i) ∧
    ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (C.shading i)

lemma mass_retention_self {d ε : ℝ} {n : ℕ} (Y : Fin n → Set Space)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hε : 0 ≤ ε) :
    ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Y i) := by
  have hh : ENNReal.ofReal (d ^ ε) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (Real.rpow_le_one hd hd1 hε)
  simpa only [one_mul] using mul_le_mul' hh (le_refl (∑ i, volume (Y i)))

theorem RetainedHierarchy.of_no_bad_gaps {d θ ε g g' gap : ℝ} {J B : ℕ}
    (C : HierarchyCertificate d θ g gap J) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : 0 ≤ ε) (hθ : θ ≤ ε) (hJB : J ≤ B)
    (hbad : (badGaps d g' J (fun j => (C.tree.layer j).radius)).card = 0) :
    RetainedHierarchy d ε g' gap B (C.tree.layer J).card C.shading := by
  let C' := (C.improve_mesh hbad).mono_error hd hd1 hθ
  exact ⟨J, C', hJB, le_rfl, Subset.rfl, mass_retention_self C.shading hd.le hd1 hε⟩

theorem RetainedHierarchy.precompose {d a b ε g gap : ℝ} {B n m : ℕ}
    {Y : Fin n → Set Space} {Z : Fin m → Set Space}
    (H : RetainedHierarchy d b g gap B m Z) (hd : 0 < d) (hd1 : d ≤ 1)
    (hb : b ≤ ε) (hε : a + b ≤ ε) (hcard : m ≤ n)
    (hsub : (⋃ i, Z i) ⊆ (⋃ i, Y i))
    (hmass : ENNReal.ofReal (d ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    RetainedHierarchy d ε g gap B n Y := by
  obtain ⟨J, C, hJB, hcn, hCY, hret⟩ := H
  exact ⟨J, C.mono_error hd hd1 hb, hJB, hcn.trans hcard, hCY.trans hsub,
    mass_retention_comp hd hd1 hε hmass hret⟩

lemma VolumeBound.of_certificate_refinement {σ ω d θ θ' g g' gap gap' κ α a : ℝ} {J J' : ℕ}
    (C : HierarchyCertificate d θ g gap J) (C' : HierarchyCertificate d θ' g' gap' J')
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 ≤ κ) (hσ : σ ≤ 1)
    (hsub : (⋃ i, C'.shading i) ⊆ (⋃ i, C.shading i))
    (hret : ENNReal.ofReal (d ^ a) * (∑ i, volume (C.shading i)) ≤ ∑ i, volume (C'.shading i))
    (hV : VolumeBound σ ω κ α d (C'.tree.layer J').card C'.shading) :
    VolumeBound σ ω (κ * (1 / 56 : ℝ) ^ (1 - σ)) (α - (θ + a) * (1 - σ))
      d (C.tree.layer J).card C.shading :=
  hV.of_refinement hd (by norm_num) hκ (C.tree.layer J).card_pos hσ
    (C.family.retained_cardinality C'.family hd hd1 hret) hsub

end WangZahlLot.Obl.wz_multiscale_finite_tower
