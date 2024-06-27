import AWFS.TAFunctors
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.EqToHom

open CategoryTheory
open Diagrams
open WalkingTriangle
open WalkingArrow
open WalkingTriangleHom
open WalkingArrowHom

set_option maxHeartbeats 300000

universe v v₂ u u₂

@[simp] theorem map_eqToHom {C : Type u₁} {D : Type u₁} [Category.{v₁} C] [Category.{v₁} D] (F : C ⥤ D)
  (X Y : C) (h : X = Y) : F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
    cases h
    simp

theorem mov_eqToHom {C : Type u₁} [Category.{v₁} C] {X X' Y: C} {h : X = X'}
  {f : X ⟶ Y} {g : X' ⟶ Y} (eq : (eqToHom h) ≫ g = f) : g = (eqToHom h.symm) ≫ f := by
    cases h
    simp
    simp at eq
    exact eq

theorem mov_eqToHom' {C : Type u₁} [Category.{v₁} C] {X X' Y: C} {h : X = X'}
  {f : Y ⟶ X} {g : Y ⟶ X'} (eq : g = f ≫ (eqToHom h)) : g ≫ (eqToHom h.symm) = f := by
    cases h
    simp
    simp at eq
    exact eq

theorem mono_eqToHom {C : Type u₁} [Category.{v₁} C] {X X': C}(h : X = X'): Mono (eqToHom h) := by
  constructor
  intros Y f g h2
  have h3 := mov_eqToHom' h2
  simp at h3
  exact h3

theorem epi_eqToHom {C : Type u₁} [Category.{v₁} C] {X X': C}(h : X = X'): Epi (eqToHom h) := by
  constructor
  intros Y f g h2
  have h3 := mov_eqToHom h2
  simp at h3
  exact h3

theorem comp_eq {C : Type u₁} [Category.{v₁} C] {X Y Z: C} {f : X ⟶ Y} {g g' : Y ⟶ Z} (h : g = g')
  : f ≫ g = f ≫ g' := by
    congr

section FactoriztionFunc

structure FactFunc (C : Type u) [Category.{v} C] where
  func : (WalkingArrow ⥤ C) ⥤ (WalkingTriangle ⥤ C)
  cond : func ⋙ PreCompMiddleFunctor = Functor.id (WalkingArrow ⥤ C)

def R {C : Type u} [Category.{v} C] (FF : FactFunc C) := (FF.func ⋙ PreCompRightFunctor)
def L {C : Type u} [Category.{v} C] (FF : FactFunc C) := (FF.func ⋙ PreCompLeftFunctor)

variable {C : Type u} [Category.{v} C] (FF : FactFunc C)

lemma eq_obj : (FF.func ⋙ PreCompMiddleFunctor).obj x = x := by
  simp [FF.cond]

@[simp]
lemma eq_LF0_F0 (F : WalkingArrow ⥤ C) : ((L FF).obj F).obj zero = F.obj zero := by
  simp [L]
  have h := congrArg (fun(x : (WalkingArrow ⥤ C) ⥤ WalkingArrow ⥤ C) => (x.obj F).obj zero) FF.cond
  simp [PreCompMiddleFunctor,MiddleFunctor,Functor.comp] at h
  exact h

@[simp]
lemma eq_RF1_F1 (F : WalkingArrow ⥤ C) : ((R FF).obj F).obj one = F.obj one := by
  simp [R]
  have h := congrArg (fun(x : (WalkingArrow ⥤ C) ⥤ WalkingArrow ⥤ C) => (x.obj F).obj one) FF.cond
  simp [PreCompMiddleFunctor,MiddleFunctor,Functor.comp] at h
  exact h

lemma eq_LF1_RF0 (F : WalkingArrow ⥤ C) : ((L  FF).obj F).obj one = ((R  FF).obj F).obj zero := by
  simp [L,R]

lemma eq_LRF0_LF1 (F : WalkingArrow ⥤ C) : ((L FF).obj ((R  FF).obj F)).obj zero = ((L  FF).obj F).obj one := by
  rw [eq_LF1_RF0]
  simp

lemma eq_RLF0_LLF1 (F : WalkingArrow ⥤ C) : ((R FF).obj ((L FF).obj F)).obj zero = ((L  FF).obj ((L  FF).obj F)).obj one := by
  rw [eq_LF1_RF0]

lemma eq_LRF1_RRF0 (F : WalkingArrow ⥤ C) : ((L FF).obj ((R FF).obj F)).obj one = ((R  FF).obj ((R  FF).obj F)).obj zero := by
  rw [eq_LF1_RF0]

lemma eq_RLF1_RF0 : ((R FF).obj ((L FF).obj F)).obj one = ((R FF).obj F).obj zero := by
  rw [<- eq_LF1_RF0]
  simp

lemma eq_F0 (F : WalkingArrow ⥤ C) : (FF.func.obj F).obj WalkingTriangle.zero = F.obj WalkingArrow.zero := by
  rw [<- eq_LF0_F0 FF]
  simp [L]

lemma eq_map_app_zero (F G: WalkingTriangle ⥤ C)(η : F ⟶ G) : (PreCompMiddleFunctor.map η).app WalkingArrow.zero = η.app WalkingTriangle.zero := by
  simp [PreCompMiddleFunctor,MiddleFunctor]

def FF_Unit : NatTrans (Functor.id (WalkingArrow ⥤ C)) (R FF) := by
  unfold R
  exact NatTrans.vcomp (eqToHom (FF.cond).symm) (NatTrans.hcomp (NatTrans.id FF.func) (@NatTrans_PCMF_PCRF C _))

def FF_CoUnit (FF : FactFunc C) : NatTrans (L  FF) (Functor.id (WalkingArrow ⥤ C)) := by
  unfold L
  exact NatTrans.vcomp (NatTrans.hcomp (NatTrans.id FF.func) (@NatTrans_PCLF_PCMF C _)) (eqToHom (FF.cond))

end FactoriztionFunc

section PreAlgWeakFactSyst

structure PreAWFS (C : Type u) [Category.{v} C] extends FactFunc C where
  multiplication : ((R toFactFunc) ⋙ (R toFactFunc)) ⟶ (R toFactFunc)
  comultiplication : (L toFactFunc) ⟶ ((L toFactFunc) ⋙ (L toFactFunc))
  Right_assoc : (multiplication ◫ (𝟙 (R toFactFunc))) ≫ multiplication = ((𝟙 (R toFactFunc)) ◫ multiplication) ≫ multiplication
  right_unit : ((FF_Unit toFactFunc) ◫ (𝟙 (R toFactFunc))) ≫ multiplication = (𝟙 (R toFactFunc))
  left_unit : ((𝟙 (R toFactFunc)) ◫ (FF_Unit toFactFunc)) ≫ multiplication = (𝟙 (R toFactFunc))
  Left_assoc : comultiplication ≫ ((𝟙 (L toFactFunc)) ◫ comultiplication) = comultiplication ≫ (comultiplication ◫ (𝟙 (L toFactFunc)))
  right_counit : comultiplication ≫ ((FF_CoUnit toFactFunc) ◫ (𝟙 (L toFactFunc))) = (𝟙 (L toFactFunc))
  left_counit : comultiplication ≫ ((𝟙 (L toFactFunc)) ◫ (FF_CoUnit toFactFunc)) = (𝟙 (L toFactFunc))

variable {C : Type u} [Category.{v} C] (preawfs : PreAWFS C)

instance : Coe (PreAWFS C) (FactFunc C) := Coe.mk PreAWFS.toFactFunc

def dist_NT_zero (F : WalkingArrow ⥤ C) : ((L preawfs).obj ((R preawfs).obj F)).obj WalkingArrow.zero ⟶ ((R preawfs).obj ((L preawfs).obj F)).obj WalkingArrow.zero := by
  let Δ := (preawfs.comultiplication.app F).app WalkingArrow.one
  have cod_eq : ((L preawfs).obj F).obj one = ((L preawfs).obj ((R preawfs).obj F)).obj zero := by
    rw [eq_LRF0_LF1]
  have dom_eq : ((R preawfs).obj ((L preawfs).obj F)).obj zero = ((L preawfs ⋙ L preawfs).obj F).obj one := by
    simp [eq_RLF0_LLF1]
  exact (eqToHom cod_eq.symm) ≫ Δ ≫ (eqToHom dom_eq.symm)

def dist_NT_one (F : WalkingArrow ⥤ C) : ((L preawfs).obj ((R preawfs).obj F)).obj WalkingArrow.one ⟶ ((R preawfs).obj ((L preawfs).obj F)).obj one := by
  let μ := (preawfs.multiplication.app F).app zero
  have cod_eq : ((R preawfs ⋙ R preawfs).obj F).obj zero = ((L preawfs).obj ((R preawfs).obj F)).obj one := by
    simp[eq_LRF1_RRF0]
  have dom_eq : ((R preawfs).obj ((L preawfs).obj F)).obj one = ((R preawfs).obj F).obj zero := by
    simp [eq_RLF1_RF0,eq_LF1_RF0]
  exact (eqToHom cod_eq.symm) ≫ μ ≫ (eqToHom dom_eq.symm)

def mul_NT (F : WalkingArrow ⥤ C) := (((evaluation (WalkingArrow ⥤ C) (WalkingArrow ⥤ C)).obj F).map preawfs.multiplication)

def comul_NT (F : WalkingArrow ⥤ C) := (((evaluation (WalkingArrow ⥤ C) (WalkingArrow ⥤ C)).obj F).map preawfs.comultiplication)

def mid_NT (F G : WalkingArrow ⥤ C) (top : (F.obj zero) ⟶ (G.obj zero))
  (bot : (F.obj one) ⟶ (G.obj one)) (h : (F.map morph) ≫ bot = top ≫ (G.map morph))
  := preawfs.func.map (Arrow.NatTrans F G top bot h)

theorem Functor_obj_eq {C : Type u₁}{D : Type u2}[Category.{v₁} C][Category.{v₂} D]
  (F G : C ⥤ D)(eq : F = G)(X : C) : (F.obj X) = (G.obj X) := by rw [eq]

theorem Functor_map_eq {C : Type u₁}{D : Type u2}[Category.{v₁} C][Category.{v₂} D]
  (F G : C ⥤ D)(eq : F = G){X Y : C}(f : X ⟶ Y)
  : (F.map f) = (eqToHom (Functor_obj_eq F G eq X)) ≫ (G.map f) ≫ (eqToHom (Functor_obj_eq F G eq Y).symm) := by
    subst F
    simp

theorem Unit_zero_L_obj_left (F : WalkingArrow ⥤ C) : ((𝟭 (WalkingArrow ⥤ C)).obj F).obj WalkingArrow.zero = ((L preawfs.toFactFunc).obj F).obj WalkingArrow.zero := by simp

theorem Unit_zero_L (F : WalkingArrow ⥤ C) : ((FF_Unit preawfs.toFactFunc).app F).app zero = eqToHom (Unit_zero_L_obj_left preawfs F) ≫ ((L preawfs).obj F).map morph ≫ (eqToHom (eq_LF1_RF0 preawfs F)):= by
  simp [FF_Unit,NatTrans_PCMF_PCRF,Right_Up,L]

lemma Unit_one_eqToHom_obj_eq (F : WalkingArrow ⥤ C) : ((R preawfs).obj F).obj one = ((𝟭 (WalkingArrow ⥤ C)).obj F).obj one := by simp

theorem Unit_one_eqToHom (F : WalkingArrow ⥤ C) : ((FF_Unit preawfs.toFactFunc).app F).app one = eqToHom (Unit_one_eqToHom_obj_eq preawfs F).symm := by
  simp [FF_Unit,NatTrans_PCMF_PCRF,Right_Up]
  rw [(preawfs.func.obj F).map_id two]
  rw [Category.comp_id]

lemma coUnit_zero_eqToHom_obj_eq (F : WalkingArrow ⥤ C) : ((L preawfs).obj F).obj zero = ((𝟭 (WalkingArrow ⥤ C)).obj F).obj zero := by simp

theorem coUnit_zero_eqToHom (F : WalkingArrow ⥤ C) : ((FF_CoUnit preawfs.toFactFunc).app F).app zero = eqToHom (coUnit_zero_eqToHom_obj_eq preawfs F) := by
  simp [FF_CoUnit,NatTrans_PCLF_PCMF,Left_Down]
  rw [(preawfs.func.obj F).map_id zero]
  rw [@Category.id_comp C _ (((preawfs.func.obj F).obj WalkingTriangle.zero))]

lemma commul_NT_zero_eqToHom_obj_eq (F : WalkingArrow ⥤ C): (((evaluation (WalkingArrow ⥤ C) (WalkingArrow ⥤ C)).obj F).obj (L preawfs)).obj zero =
  (((evaluation (WalkingArrow ⥤ C) (WalkingArrow ⥤ C)).obj F).obj (L preawfs ⋙ L preawfs)).obj zero := by simp

theorem commul_NT_zero_eqToHom (F : WalkingArrow ⥤ C) : (comul_NT preawfs F).app WalkingArrow.zero =
  eqToHom (commul_NT_zero_eqToHom_obj_eq preawfs F) := by
    simp [comul_NT]
    have u := mono_eqToHom (coUnit_zero_eqToHom_obj_eq preawfs ((L preawfs).obj F))
    rw [<-  coUnit_zero_eqToHom] at u
    apply (u.right_cancellation ((preawfs.comultiplication.app F).app WalkingArrow.zero))
    have h1 : (preawfs.comultiplication.app F).app zero ≫
      ((FF_CoUnit preawfs.toFactFunc).app ((L preawfs.toFactFunc).obj F)).app zero =
      ((preawfs.comultiplication.app F) ≫ ((FF_CoUnit preawfs.toFactFunc).app ((L preawfs.toFactFunc).obj F))).app zero
      := by simp
    rw [h1]
    have h2 : ((FF_CoUnit preawfs).app ((L preawfs).obj F)) = ((𝟙 (L preawfs)) ◫ (FF_CoUnit preawfs.toFactFunc)).app F := by simp
    rw [h2]
    have h3 : (preawfs.comultiplication.app F ≫ (𝟙 (L preawfs) ◫ FF_CoUnit preawfs).app F) = (preawfs.comultiplication ≫ ((𝟙 (L preawfs.toFactFunc)) ◫ (FF_CoUnit preawfs.toFactFunc))).app F := by simp
    rw [h3,preawfs.left_counit,<-h2, coUnit_zero_eqToHom]
    simp [NatTrans.id]

lemma mul_NT_zero_eqToHom_ob_eq (G : WalkingArrow ⥤ C) : (preawfs.func.obj ((R preawfs.toFactFunc).obj G)).obj WalkingTriangle.zero =
  (((evaluation (WalkingArrow ⥤ C) (WalkingArrow ⥤ C)).obj G).obj (R preawfs.toFactFunc)).obj WalkingArrow.zero := by
    rw [<- PCMF_obj_zero]
    have h1 := Functor.congr_obj preawfs.cond ((R preawfs.toFactFunc).obj G)
    simp [Functor.comp] at h1
    rw [h1]
    simp

theorem mul_NT_zero_eqToHom (G : WalkingArrow ⥤ C) :
  (preawfs.func.obj ((R preawfs.toFactFunc).obj G)).map left ≫ (mul_NT preawfs G).app WalkingArrow.zero = eqToHom (mul_NT_zero_eqToHom_ob_eq preawfs G) := by
  simp [mul_NT]
  have u := mov_eqToHom' (mov_eqToHom (Unit_zero_L preawfs ((R preawfs).obj G)).symm).symm
  simp [L] at u
  rw [u.symm,Category.assoc]
  have eq1 : ((FF_Unit preawfs.toFactFunc).app ((R preawfs.toFactFunc).obj G)).app zero ≫
      (preawfs.multiplication.app G).app zero = (((FF_Unit preawfs.toFactFunc).app ((R preawfs.toFactFunc).obj G)) ≫
      (preawfs.multiplication.app G)).app zero := by simp
  rw [eq1]
  have eq2 : ((FF_Unit preawfs.toFactFunc).app ((R preawfs.toFactFunc).obj G)) = ((𝟙 (R preawfs))◫ (FF_Unit preawfs)).app G := by
    simp
  rw[eq2]
  have eq3 : ((𝟙 (R preawfs.toFactFunc) ◫ FF_Unit preawfs.toFactFunc).app G ≫ preawfs.multiplication.app G) = ((𝟙 (R preawfs.toFactFunc) ◫ FF_Unit preawfs.toFactFunc) ≫ preawfs.multiplication).app G := by simp
  rw [eq3, preawfs.left_unit]
  simp

theorem mid_NT_top_eqToHom {F G : WalkingArrow ⥤ C} {top : (F.obj zero) ⟶ (G.obj zero)}
  {bot : (F.obj one) ⟶ (G.obj one)} {h : (F.map morph) ≫ bot = top ≫ (G.map morph)}
  : (mid_NT awfs (F) (G) top bot h).app zero =  (eqToHom (eq_F0 awfs F)) ≫ top ≫ (eqToHom (eq_F0 awfs G).symm) := by
    rw [<- eq_map_app_zero]
    have c := awfs.cond
    simp [mid_NT]
    have eq1 : (PreCompMiddleFunctor.map (awfs.func.map (Arrow.NatTrans F G top bot h))) = (awfs.func ⋙ PreCompMiddleFunctor).map (Arrow.NatTrans F G top bot h) := by
      simp [Functor.comp]
    rw [eq1]
    rw [Functor_map_eq (awfs.func ⋙ PreCompMiddleFunctor) (𝟭 (WalkingArrow ⥤ C)) c _]
    simp [Functor.id,Arrow.NatTrans]


def Lift (F G : WalkingArrow ⥤ C) (top : (((L preawfs).obj F).obj zero) ⟶ (((R preawfs).obj G).obj zero))
  (bot : (((L preawfs).obj F).obj one) ⟶ (((R preawfs).obj G).obj one)) (h : (((L preawfs).obj F).map morph) ≫ bot = top ≫ (((R preawfs).obj G).map morph))
  : (((L preawfs).obj F).obj one) ⟶ (((R preawfs).obj G).obj zero)
  := (comul_NT preawfs F).app one ≫ (mid_NT preawfs ((@L C _ preawfs).obj F) ((@R C _ preawfs).obj G) top bot h).app one ≫ (mul_NT preawfs G).app zero

instance preawfs_Monad : CategoryTheory.Monad (WalkingArrow ⥤ C) where
  toFunctor := (R preawfs)
  η' := (FF_Unit preawfs)
  μ' := preawfs.multiplication
  assoc' := by
    intro X
    have h' := congrArg (fun(z) => z.app X) preawfs.Right_assoc
    simp at h'
    refine h'
  left_unit' := by
    intro X
    have h' := congrArg (fun(z) => z.app X) preawfs.left_unit
    simp at h'
    simp
    refine h'
  right_unit' := by
    intro X
    have h' := congrArg (fun(z) => z.app X) preawfs.right_unit
    simp at h'
    simp
    refine h'

instance preawfs_CoMonad : CategoryTheory.Comonad (WalkingArrow ⥤ C) where
  toFunctor := (L preawfs)
  ε' := @FF_CoUnit C _ preawfs
  δ' := preawfs.comultiplication
  coassoc' := by
    intro X
    have h' := congrArg (fun(z) => z.app X) preawfs.Left_assoc.symm
    simp at h'
    refine h'
  left_counit' := by
    intro X
    have h' := congrArg (fun(z) => z.app X) preawfs.left_counit
    simp at h'
    simp
    refine h'
  right_counit' := by
    intro X
    have h' := congrArg (fun(z) => z.app X) preawfs.right_counit
    simp at h'
    simp
    refine h'

end PreAlgWeakFactSyst

section AlgWeakFactSyst

structure AWFS (C : Type u) [Category.{v} C] extends PreAWFS C where
  distribution : ∀(F : WalkingArrow ⥤ C), ((L toPreAWFS).obj ((R toPreAWFS).obj F)).map morph ≫ (dist_NT_one toPreAWFS F) = (dist_NT_zero toPreAWFS F) ≫ ((R toPreAWFS).obj ((L toPreAWFS).obj F)).map morph

variable {C : Type u} [Category.{v} C] (awfs : AWFS C)

instance : Coe (AWFS C) (PreAWFS C) := Coe.mk AWFS.toPreAWFS

lemma help (F : _): (((L awfs) ⋙ (L awfs)).obj F).map morph = (awfs.func.obj ((L awfs).obj F)).map left := by simp [L]
lemma help' (G : _): (((R awfs) ⋙ (R awfs)).obj G).map morph = (awfs.func.obj ((R awfs).obj G)).map right := by simp [R]


theorem Lift_upper (F G : WalkingArrow ⥤ C) (top : (((L awfs).obj F).obj zero) ⟶ (((R awfs).obj G).obj zero))
  (bot : (((L awfs).obj F).obj one) ⟶ (((R awfs).obj G).obj one)) (h : (((L awfs).obj F).map morph) ≫ bot = top ≫ (((R awfs).obj G).map morph))
  :(((L awfs).obj F).map morph) ≫ (Lift awfs F G top bot h) = top := by
    unfold Lift
    have h1 := (comul_NT awfs F).naturality morph
    unfold evaluation at h1
    rw [<- Category.assoc,h1,Category.assoc]
    have h2 := (mid_NT awfs ((@L C _ awfs).obj F) ((@R C _ awfs).obj G) top bot h).naturality left
    rw [<- help] at h2
    rw [<- Category.assoc (((L awfs.toFactFunc ⋙ L awfs.toFactFunc).obj F).map morph),h2,Category.assoc]
    rw [mid_NT_top_eqToHom,commul_NT_zero_eqToHom,mul_NT_zero_eqToHom]
    simp

theorem Lift_lower (F G : WalkingArrow ⥤ C) (top : (((L awfs).obj F).obj zero) ⟶ (((R awfs).obj G).obj zero))
  (bot : (((L awfs).obj F).obj one) ⟶ (((R awfs).obj G).obj one)) (h : (((L awfs).obj F).map morph) ≫ bot = top ≫ (((R awfs).obj G).map morph))
  :(Lift awfs F G top bot h) ≫ (((R awfs).obj G).map morph) = bot := by
    unfold Lift
    rw [Category.assoc,Category.assoc]
    have h1 := (mul_NT awfs G).naturality morph
    unfold evaluation at h1
    rw [<- h1]
    simp only [Prefunctor.obj]
    have h2 := (mid_NT awfs ((@L C _ awfs).obj F) ((@R C _ awfs).obj G) top bot h).naturality right
    simp only [Prefunctor.obj] at h2
    rw [<- help'] at h2
    rw [<- Category.assoc ((mid_NT awfs.toPreAWFS ((L awfs.toFactFunc).obj F) ((R awfs.toFactFunc).obj G) top bot h).app WalkingTriangle.one)]
    rw [<- h2]
    sorry
