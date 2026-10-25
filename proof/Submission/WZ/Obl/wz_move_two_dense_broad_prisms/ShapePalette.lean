-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.ShapePalette.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DenseSelection

/-! Joint finite labels for the wide and narrow prism constructions. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

def PrismPiece.relabel {n N J J' : ℕ} (B : PrismPiece n N J) (f : Fin J → Fin J') :
    PrismPiece n N J' :=
  ⟨f B.scale, B.coarse, B.center, B.frame, B.piece⟩

lemma PrismPiece.Good.relabel {n N J J' : ℕ} {ω ζ d h a c s : ℝ}
    {ρ : Fin J → ℝ} {ρ' : Fin J' → ℝ} {x v : Fin n → V} {y w : Fin N → V}
    {B : PrismPiece n N J} (hB : B.Good ω ζ d h a c s ρ x v y w)
    (f : Fin J → Fin J') (hρ : ∀ j, ρ' (f j) = ρ j) :
    (B.relabel f).Good ω ζ d h a c s ρ' x v y w := by
  simpa only [PrismPiece.Good, PrismPiece.relabel, hρ] using hB

def thicknessPalette (d a : ℝ) (K : ℕ) : Fin ((K+1)+(K+1)) → ℝ :=
  Fin.addCases (fun _ => 10000000000*a) (fun _ => 10000*d)

def lengthPalette (d L : ℝ) (K : ℕ) : Fin ((K+1)+(K+1)) → ℝ :=
  Fin.addCases (fun _ => 10*L) (fun k => 10*(d/((1/2:ℝ)^(k:ℕ))))

def broadnessPalette (d a L : ℝ) (K : ℕ) : Fin ((K+1)+(K+1)) → ℝ :=
  Fin.addCases (fun k => packetWidth (10000*a) L ((1/2:ℝ)^(k:ℕ))/(10*L))
    (fun k => 1000*((1/2:ℝ)^(k:ℕ)))

lemma wide_piece_relabel {n N K : ℕ} {ω ζ d h a L s : ℝ}
    {x v : Fin n → V} {y w : Fin N → V} {Q : PrismPiece n N (K+1)}
    (hQ : Q.Good ω ζ d h (1000000*(10000*a)) (10*L) s
      (fun k => packetWidth (10000*a) L ((1/2:ℝ)^(k:ℕ))/(10*L)) x v y w) :
    (Q.relabel (Fin.castAdd (K+1))).Good ω ζ d h
      (thicknessPalette d a K (Q.relabel (Fin.castAdd (K+1))).scale)
      (lengthPalette d L K (Q.relabel (Fin.castAdd (K+1))).scale) s
      (broadnessPalette d a L K) x v y w := by
  have hh := hQ.relabel (Fin.castAdd (K+1))
    (ρ' := broadnessPalette d a L K) (fun k => by simp only [broadnessPalette, Fin.addCases_left, Fin.addCases_right])
  simpa only [PrismPiece.relabel, thicknessPalette, lengthPalette, Fin.addCases_left,
    show 1000000*(10000*a) = 10000000000*a by ring] using hh

lemma narrow_piece_relabel {n N K : ℕ} {ω ζ d h a L s : ℝ}
    {x v : Fin n → V} {y w : Fin N → V} {Q : PrismPiece n N (K+1)}
    (hQ : Q.Good ω ζ d h (10000*d) (10*(d/((1/2:ℝ)^(Q.scale:ℕ)))) s
      (fun k => 1000*((1/2:ℝ)^(k:ℕ))) x v y w) :
    (Q.relabel (Fin.natAdd (K+1))).Good ω ζ d h
      (thicknessPalette d a K (Q.relabel (Fin.natAdd (K+1))).scale)
      (lengthPalette d L K (Q.relabel (Fin.natAdd (K+1))).scale) s
      (broadnessPalette d a L K) x v y w := by
  have hh := hQ.relabel (Fin.natAdd (K+1))
    (ρ' := broadnessPalette d a L K) (fun k => by simp only [broadnessPalette, Fin.addCases_left, Fin.addCases_right])
  simpa only [PrismPiece.relabel, thicknessPalette, lengthPalette, Fin.addCases_right] using hh

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
