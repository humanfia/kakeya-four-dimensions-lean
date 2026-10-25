-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NormalStripCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NormalStripCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ShearedSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.StripCounts

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NormalStripCensus

open Set ShearedSupport

noncomputable section

def normal (row : Fin 3 → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  x 3-∑ j, row j*x j.castSucc

def strip (row : Fin 3 → ℝ) (p : ℝ) (x : Fin 4 → ℝ) : ℤ :=
  ⌊normal row x/p⌋

theorem normal_distance {p B : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (row : Fin 3 → ℝ) (hrow : ∀ j, |row j| ≤ B)
    {x y : Fin 4 → ℝ} (hcode : code p x=code p y) :
    |normal row x-normal row y| ≤ (1+3*B)*p := by
  have hbase (j : Fin 3) : |x j.castSucc-y j.castSucc| ≤ p :=
    same_cell_distance hp (congrArg (fun q : Code => q.1 j) hcode)
  have hheight : |x 3-y 3| ≤ p := same_cell_distance hp (congrArg Prod.snd hcode)
  have hsum : |∑ j : Fin 3, row j*(x j.castSucc-y j.castSucc)| ≤ 3*B*p := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j : Fin 3, B*p := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hrow j) (hbase j) (abs_nonneg _) hB
      _ = 3*B*p := by simp; ring
  have heq : normal row x-normal row y =
      (x 3-y 3)-∑ j, row j*(x j.castSucc-y j.castSucc) := by
    simp only [normal,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hheight hsum).trans_eq (by ring))

/-- A single physical cell meets only a bounded number of normal
strips. The normal and every counted strip have actual point witnesses. -/
theorem strip_multiplicity (N : Finset ℤ) (row : Fin 3 → ℝ)
    {p B : ℝ} (hp : 0 < p) (hB : 0 ≤ B) (hrow : ∀ j, |row j| ≤ B)
    (q : Code) (hwitness : ∀ n ∈ N, ∃ x : Fin 4 → ℝ, code p x=q ∧ strip row p x=n) :
    (N.card : ℝ) ≤ 8+6*B := by
  apply (Submission.Lib.K4ScalarProfileAmplitude.Scalar.card_int_grid_of_diameter N
    (show 0 ≤ 3+3*B by positivity) ?_).trans_eq (by ring)
  intro i hi j hj
  obtain ⟨x,hx,hxi⟩ := hwitness i hi
  obtain ⟨y,hy,hyj⟩ := hwitness j hj
  have hh := floor_distance hp (normal_distance hp hB row hrow (hx.trans hy.symm))
  change |(strip row p x : ℝ)-(strip row p y : ℝ)| ≤ _ at hh
  rw [hxi,hyj] at hh
  exact hh.trans_eq (by field_simp; ring)

/-- Filling base cells in each actual strip, combined with hereditary
physical support, gives the scalar strip count. Both the joint cell
carriers and their multiplicities are constructed here. -/
theorem count_from_actual_filling {Ω : Type*}
    (E : Set Ω) (X : Ω → Fin 4 → ℝ) (row corner : Fin 3 → ℝ)
    (coarsen : Code → Code) (base : Ω → Fin 3 → ℤ) (baseMap : Code → Fin 3 → ℤ)
    (N : Finset ℤ) {H ρ r p B K Kfill dimension center : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hp : 0 < p) (hrH : r ≤ H)
    (hB : 1 ≤ B) (hK : 0 ≤ K) (hfillK : 0 < Kfill)
    (hrow : ∀ j, |row j| ≤ B)
    (hfactor : ∀ z ∈ E, code r (X z)=coarsen (code p (X z)))
    (hbase : ∀ z ∈ E, base z=baseMap (code p (X z)))
    (hbox : ∀ z ∈ E, ∀ j : Fin 3, |X z j.castSucc-corner j| ≤ H)
    (hslab : ∀ z ∈ E, |normal row (X z)-center| ≤ r)
    (htables : ∀ q : Code, ∃ F : Finset Code,
      (F.card : ℝ) ≤ K*(r/p)^((3:ℝ)+dimension) ∧
      ∀ z ∈ E, code r (X z)=q → code p (X z)∈F)
    (hfill : ∀ n ∈ N, ∃ W : Finset (Fin 3 → ℤ),
      (ρ/p)^3/Kfill ≤ (W.card : ℝ) ∧
      ∀ w ∈ W, ∃ z ∈ E, strip row p (X z)=n ∧ base z=w) :
    (N.card : ℝ) ≤ 22000*B*K*Kfill*(8+6*B)*(H/ρ)^3*(r/p)^dimension := by
  classical
  obtain ⟨F,hF,hFcover,hFwitness⟩ := exists_slab_support E X row corner coarsen
    hr hp hrH hB hK hrow hfactor hbox hslab htables
  let W : ℤ → Finset Code := fun n => F.filter
    (fun q => ∃ z ∈ E, code p (X z)=q ∧ strip row p (X z)=n)
  have hWsub (n : ℤ) (_hn : n ∈ N) : W n ⊆ F := Finset.filter_subset _ _
  have hWfill (n : ℤ) (hn : n ∈ N) : (ρ/p)^3/Kfill ≤ ((W n).card : ℝ) := by
    obtain ⟨A,hA,hAwitness⟩ := hfill n hn
    have hsub : A ⊆ (W n).image baseMap := by
      intro a ha
      obtain ⟨z,hz,hzn,hza⟩ := hAwitness a ha
      refine Finset.mem_image.mpr ⟨code p (X z),?_,(hbase z hz).symm.trans hza⟩
      exact Finset.mem_filter.mpr ⟨hFcover z hz,z,hz,rfl,hzn⟩
    exact hA.trans ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (Nat.cast_le.mpr Finset.card_image_le))
  have hmult (q : Code) (_hq : q ∈ F) :
      ((N.filter fun n => q ∈ W n).card : ℝ) ≤ 8+6*B := by
    apply strip_multiplicity _ row hp (zero_le_one.trans hB) hrow q
    intro n hn
    obtain ⟨z,hz,hzq,hzn⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).2).2
    exact ⟨X z,hzq,hzn⟩
  have hcount := weighted_witness_count N F W (fun _ => (1:ℝ)) ((ρ/p)^3/Kfill) (8+6*B)
    (fun _ _ => zero_le_one) hWsub
    (fun n hn => by simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hWfill n hn) hmult
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hcount
  have hcount' : (N.card : ℝ)*((ρ/p)^3/Kfill) ≤
      (8+6*B)*(22000*B*K*(H/r)^3*(r/p)^((3:ℝ)+dimension)) :=
    hcount.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  have heq : (8+6*B)*(22000*B*K*(H/r)^3*(r/p)^((3:ℝ)+dimension)) =
      (22000*B*K*Kfill*(8+6*B)*(H/ρ)^3*(r/p)^dimension)*((ρ/p)^3/Kfill) := by
    rw [Real.rpow_add (div_pos hr hp)]
    rw [show (r/p)^(3:ℝ)=(r/p)^(3:ℕ) by norm_num]
    simp only [div_pow]
    field_simp [hp.ne',hr.ne',hρ.ne',hfillK.ne']
    <;> ring
  rw [heq] at hcount'
  exact (mul_le_mul_iff_left₀ (div_pos (pow_pos (div_pos hρ hp) 3) hfillK)).mp hcount'

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NormalStripCensus
