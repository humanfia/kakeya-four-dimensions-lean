-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CertificateMonotonicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.ReferenceGain

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

noncomputable def HierarchyCertificate.mono_error {d θ θ' g gap : ℝ} {J : ℕ}
    (C : HierarchyCertificate d θ g gap J) (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ') :
    HierarchyCertificate d θ' g gap J where
  tree := C.tree
  shading := C.shading
  root_axis := C.root_axis
  scalar := C.scalar
  control := C.control.mono_error hd hd1 hθ
  alignment := C.alignment
  family := C.family.mono (Real.rpow_le_rpow_of_exponent_ge hd hd1 hθ)
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ))
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ))

noncomputable def HierarchyCertificate.weaken_gap {d θ g gap gap' : ℝ} {J : ℕ}
    (C : HierarchyCertificate d θ g gap J) (hd : 0 < d) (hd1 : d ≤ 1) (hgap : gap' ≤ gap) :
    HierarchyCertificate d θ g gap' J where
  tree := C.tree
  shading := C.shading
  root_axis := C.root_axis
  scalar := C.scalar
  control := C.control.weaken_gap hd hd1 hgap
  alignment := C.alignment
  family := C.family

lemma mass_retention_comp {d a b ε : ℝ} {n m l : ℕ}
    {Y : Fin n → Set Space} {Z : Fin m → Set Space} {W : Fin l → Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1) (hε : a + b ≤ ε)
    (hYZ : ENNReal.ofReal (d ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (hZW : ENNReal.ofReal (d ^ b) * (∑ i, volume (Z i)) ≤ ∑ i, volume (W i)) :
    ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) := by
  calc
    _ ≤ ENNReal.ofReal (d ^ (a + b)) * (∑ i, volume (Y i)) := mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hd hd1 hε)) le_rfl
    _ = ENNReal.ofReal (d ^ b) * (ENNReal.ofReal (d ^ a) * (∑ i, volume (Y i))) := by
      rw [Real.rpow_add hd, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
      ac_rfl
    _ ≤ ENNReal.ofReal (d ^ b) * (∑ i, volume (Z i)) := mul_le_mul' le_rfl hYZ
    _ ≤ _ := hZW

end WangZahlLot.Obl.wz_multiscale_finite_tower
