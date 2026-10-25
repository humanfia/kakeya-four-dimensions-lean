-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ShearedSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ShearedSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.HereditaryClockSupport
import Submission.Lib.K4IncidenceWitnesses
import Submission.Lib.K4ScalarProfileAmplitude.Scalar.Grid

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ShearedSupport

open Set

noncomputable section

abbrev Code := (Fin 3 → ℤ) × ℤ

def code (r : ℝ) (x : Fin 4 → ℝ) : Code :=
  (fun j => ⌊x j.castSucc / r⌋, ⌊x 3 / r⌋)

/-- A floor loses at most two units when a real distance is divided by
the mesh. No alignment of the two centers is needed. -/
theorem floor_distance {r D x y : ℝ} (hr : 0 < r) (hxy : |x-y| ≤ D) :
    |(⌊x/r⌋ : ℝ)-(⌊y/r⌋ : ℝ)| ≤ D/r+2 := by
  have hx : |(⌊x/r⌋ : ℝ)-x/r| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Int.floor_le (x/r),Int.lt_floor_add_one (x/r)]
  have hy : |y/r-(⌊y/r⌋ : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Int.floor_le (y/r),Int.lt_floor_add_one (y/r)]
  have hd : |(x-y)/r| ≤ D/r := by
    rw [abs_div,abs_of_pos hr]
    exact div_le_div_of_nonneg_right hxy hr.le
  have heq : (⌊x/r⌋ : ℝ)-(⌊y/r⌋ : ℝ) =
      ((⌊x/r⌋ : ℝ)-x/r)+(x-y)/r+(y/r-(⌊y/r⌋ : ℝ)) := by ring
  rw [heq]
  calc
    _ ≤ |(⌊x/r⌋ : ℝ)-x/r+(x-y)/r|+|y/r-(⌊y/r⌋ : ℝ)| := abs_add_le _ _
    _ ≤ (|(⌊x/r⌋ : ℝ)-x/r|+|(x-y)/r|)+|y/r-(⌊y/r⌋ : ℝ)| :=
      add_le_add (abs_add_le ((⌊x/r⌋ : ℝ)-x/r) ((x-y)/r)) le_rfl
    _ ≤ (1+D/r)+1 := add_le_add (add_le_add hx hd) hy
    _ = D/r+2 := by ring

theorem same_cell_distance {r x y : ℝ} (hr : 0 < r)
    (h : ⌊x/r⌋ = ⌊y/r⌋) : |x-y| ≤ r := by
  have hh := (Int.abs_sub_lt_one_of_floor_eq_floor h).le
  rw [←sub_div,abs_div,abs_of_pos hr,div_le_iff₀ hr] at hh
  simpa only [one_mul] using hh

/-- Count coarse physical cells in a base box and one sloping slab.
The bound is cubic in the base size; the shear costs only a fixed
power of the row bound. -/
theorem coarse_slab_card (S : Finset Code) (row corner : Fin 3 → ℝ)
    {H r B center : ℝ} (hr : 0 < r) (hrH : r ≤ H) (hB : 1 ≤ B)
    (hrow : ∀ j, |row j| ≤ B)
    (hwitness : ∀ q ∈ S, ∃ x : Fin 4 → ℝ, code r x=q ∧
      (∀ j : Fin 3, |x j.castSucc-corner j| ≤ H) ∧
      |x 3-∑ j, row j*x j.castSucc-center| ≤ r) :
    (S.card : ℝ) ≤ 22000*B*(H/r)^3 := by
  classical
  have hH : 0 < H := hr.trans_le hrH
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hbase : ((S.image Prod.fst).card : ℝ) ≤ (4*H/r+7)^3 := by
    have hh := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
      (S.image Prod.fst) (show 0 ≤ 2*H/r+2 by positivity) (by
        intro a ha b hb j
        obtain ⟨qa,hqa,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨qb,hqb,rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨x,hx,hxbox,-⟩ := hwitness qa hqa
        obtain ⟨y,hy,hybox,-⟩ := hwitness qb hqb
        have hxy : |x j.castSucc-y j.castSucc| ≤ 2*H := by
          exact (abs_sub_le _ (corner j) _).trans (by
            rw [abs_sub_comm (corner j)]
            linarith [hxbox j,hybox j])
        have hh := floor_distance hr hxy
        have hxj := congrFun (congrArg Prod.fst hx) j
        have hyj := congrFun (congrArg Prod.fst hy) j
        change ⌊x j.castSucc/r⌋=qa.1 j at hxj
        change ⌊y j.castSucc/r⌋=qb.1 j at hyj
        simpa only [hxj,hyj] using hh)
    simpa only [Fintype.card_fin,show 2*(2*H/r+2)+3=4*H/r+7 by ring] using hh
  have hfiber (a : Fin 3 → ℤ) :
      ((S.filter fun q => q.1=a).card : ℝ) ≤ 10+6*B := by
    let F := S.filter fun q => q.1=a
    have hinj : Set.InjOn Prod.snd (F : Set Code) := by
      intro q hq q' hq' heq
      apply Prod.ext
      · exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq').2.symm
      · exact heq
    have hcard : (F.image Prod.snd).card = F.card := Finset.card_image_of_injOn hinj
    rw [←hcard]
    apply (Submission.Lib.K4ScalarProfileAmplitude.Scalar.card_int_grid_of_diameter
      (F.image Prod.snd) (show 0 ≤ 4+3*B by positivity) ?_).trans_eq (by ring)
    intro i hi j hj
    obtain ⟨qi,hqi,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨qj,hqj,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨x,hx,-,hxslab⟩ := hwitness qi (Finset.mem_filter.mp hqi).1
    obtain ⟨y,hy,-,hyslab⟩ := hwitness qj (Finset.mem_filter.mp hqj).1
    have hxy (e : Fin 3) : |x e.castSucc-y e.castSucc| ≤ r := by
      apply same_cell_distance hr
      have he := congrArg (fun q : Code => q.1 e) hx
      have he' := congrArg (fun q : Code => q.1 e) hy
      change ⌊x e.castSucc/r⌋=qi.1 e at he
      change ⌊y e.castSucc/r⌋=qj.1 e at he'
      rw [he,he',(Finset.mem_filter.mp hqi).2,(Finset.mem_filter.mp hqj).2]
    have hsum : |∑ e : Fin 3, row e*(x e.castSucc-y e.castSucc)| ≤ 3*B*r := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ _e : Fin 3, B*r := by
          apply Finset.sum_le_sum
          intro e _
          rw [abs_mul]
          exact mul_le_mul (hrow e) (hxy e) (abs_nonneg _) hB0
        _ = 3*B*r := by simp; ring
    have hheight : |x 3-y 3| ≤ (2+3*B)*r := by
      have heq : x 3-y 3 =
          (x 3-∑ e, row e*x e.castSucc-center)-
          (y 3-∑ e, row e*y e.castSucc-center)+
          ∑ e, row e*(x e.castSucc-y e.castSucc) := by
        simp only [mul_sub,Finset.sum_sub_distrib]
        ring
      rw [heq]
      calc
        _ ≤ |(x 3-∑ e, row e*x e.castSucc-center)-
            (y 3-∑ e, row e*y e.castSucc-center)|+
            |∑ e, row e*(x e.castSucc-y e.castSucc)| := abs_add_le _ _
        _ ≤ (|x 3-∑ e, row e*x e.castSucc-center|+
            |y 3-∑ e, row e*y e.castSucc-center|)+
            |∑ e, row e*(x e.castSucc-y e.castSucc)| :=
          add_le_add (abs_sub (x 3-∑ e, row e*x e.castSucc-center)
            (y 3-∑ e, row e*y e.castSucc-center)) le_rfl
        _ ≤ (r+r)+3*B*r := add_le_add (add_le_add hxslab hyslab) hsum
        _ = (2+3*B)*r := by ring
    have hh := floor_distance hr hheight
    have hxi := congrArg Prod.snd hx
    have hyj := congrArg Prod.snd hy
    change ⌊x 3/r⌋=qi.2 at hxi
    change ⌊y 3/r⌋=qj.2 at hyj
    rw [hxi,hyj] at hh
    have heq : ((2+3*B)*r)/r+2=4+3*B := by field_simp; ring
    exact hh.trans_eq heq
  have htotal := Submission.Lib.K4ScalarProfileAmplitude.Scalar.card_le_image_mul_fiber
    S Prod.fst (10+6*B) (fun a _ => hfiber a)
  have hratio : 1 ≤ H/r := (one_le_div hr).mpr hrH
  calc
    (S.card : ℝ) ≤ ((S.image Prod.fst).card : ℝ)*(10+6*B) := htotal
    _ ≤ (4*H/r+7)^3*(10+6*B) := mul_le_mul_of_nonneg_right hbase (by positivity)
    _ ≤ (11*(H/r))^3*(16*B) := by
      gcongr
      · rw [show 4*H/r=4*(H/r) by ring]
        linarith only [hratio]
      · linarith
    _ ≤ 22000*B*(H/r)^3 := by
      calc
        _ = 21296*B*(H/r)^3 := by ring
        _ ≤ 22000*B*(H/r)^3 := by gcongr <;> norm_num

/-- Local hereditary tables count all fine physical cells in a sloping
slab. The table and the finite carrier are constructed from the actual
point set, independently of later choices of strip witnesses. -/
theorem exists_slab_support {Ω : Type*} (E : Set Ω) (X : Ω → Fin 4 → ℝ)
    (row corner : Fin 3 → ℝ) (coarsen : Code → Code)
    {H r p B K dimension center : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hrH : r ≤ H) (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hrow : ∀ j, |row j| ≤ B)
    (hfactor : ∀ z ∈ E, code r (X z)=coarsen (code p (X z)))
    (hbox : ∀ z ∈ E, ∀ j : Fin 3, |X z j.castSucc-corner j| ≤ H)
    (hslab : ∀ z ∈ E, |X z 3-∑ j, row j*X z j.castSucc-center| ≤ r)
    (htables : ∀ q : Code, ∃ F : Finset Code,
      (F.card : ℝ) ≤ K*(r/p)^((3:ℝ)+dimension) ∧
      ∀ z ∈ E, code r (X z)=q → code p (X z)∈F) :
    ∃ F : Finset Code,
      (F.card : ℝ) ≤ 22000*B*K*(H/r)^3*(r/p)^((3:ℝ)+dimension) ∧
      (∀ z ∈ E, code p (X z)∈F) ∧
      ∀ q ∈ F, ∃ z ∈ E, code p (X z)=q := by
  classical
  let occupied : Set Code := {q | ∃ z ∈ E, code p (X z)=q}
  let bound := 22000*B*K*(H/r)^3*(r/p)^((3:ℝ)+dimension)
  have hcount (S : Finset Code) (hS : (S : Set Code) ⊆ occupied) :
      (S.card : ℝ) ≤ bound := by
    let C := S.image coarsen
    have hC : (C.card : ℝ) ≤ 22000*B*(H/r)^3 := by
      apply coarse_slab_card C row corner hr hrH hB hrow
      intro q hq
      obtain ⟨fine,hfine,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨z,hz,hcode⟩ := hS hfine
      refine ⟨X z,?_,hbox z hz,hslab z hz⟩
      rw [hfactor z hz,hcode]
    have hfiber (q : Code) :
        ((S.filter fun k => coarsen k=q).card : ℝ) ≤ K*(r/p)^((3:ℝ)+dimension) := by
      obtain ⟨F,hF,hcover⟩ := htables q
      apply (show ((S.filter fun k => coarsen k=q).card : ℝ) ≤ (F.card : ℝ) from
        Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hF
      intro k hk
      obtain ⟨z,hz,hcode⟩ := hS (Finset.mem_filter.mp hk).1
      rw [←hcode]
      apply hcover z hz
      rw [hfactor z hz,hcode]
      exact (Finset.mem_filter.mp hk).2
    have htotal := Submission.Lib.K4ScalarProfileAmplitude.Scalar.card_le_image_mul_fiber
      S coarsen (K*(r/p)^((3:ℝ)+dimension)) (fun q _ => hfiber q)
    apply htotal.trans
    apply (mul_le_mul_of_nonneg_right hC (mul_nonneg hK (Real.rpow_nonneg (div_pos hr hp).le _))).trans_eq
    dsimp only [bound]
    ring
  have hfinite := Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
    occupied bound hcount
  refine ⟨hfinite.toFinset,?_,?_,?_⟩
  · exact hcount _ (by simp)
  · intro z hz
    exact hfinite.mem_toFinset.mpr ⟨z,hz,rfl⟩
  · intro q hq
    exact hfinite.mem_toFinset.mp hq

/-- Exact dyadic nesting supplies the factor map in the preceding
construction, so no additional code compatibility certificate is needed. -/
theorem code_dyadic_coarsens {Ω : Type*} (X : Ω → Fin 4 → ℝ)
    (p : ℝ) (steps : ℕ) (z : Ω) :
    code (p*(2:ℝ)^steps) (X z) =
      ParentSource.coarsenProductGrid steps steps (code p (X z)) := by
  exact HereditaryClockSupport.product_code_coarsens
    (fun z j => X z j.castSucc) (fun z => X z 3) p p steps steps z

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ShearedSupport
