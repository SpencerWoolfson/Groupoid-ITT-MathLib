import Mathlib.CategoryTheory.Groupoid.Subgroupoid
import Mathlib.CategoryTheory.EssentialImage
import Groupoids.Gpd
import AWFS.TAFunctors
import AWFS.AWFS
import Mathlib.CategoryTheory.Comma.Basic

set_option maxHeartbeats 450000

universe v u

namespace CategoryTheory

def Functor_obj_eq {C : Type u₁}{D : Type u₂}[Category.{v₁} C][Category.{v₂} D]{x y : C}
  (F : C ⥤ D)(h : x = y) : (F.obj x) = (F.obj y) := congrArg F.obj h

def Comma.ext {C : Type u₁}{D : Type u₂}{E : Type u₃}[Category.{v₁} C][Category.{v₂} D][Category.{v₃} E]
  {F : C ⥤ E}{G : D ⥤ E}(x y: Comma F G)(hl : x.left = y.left)(hr : x.right = y.right)
  (h_hom : x.hom = (eqToHom (congrArg F.obj hl)) ≫ y.hom ≫ (eqToHom (congrArg G.obj hr.symm))) : x = y := by
  rcases x with ⟨xl,xr,xh⟩
  rcases y with ⟨yl,yr,yh⟩
  congr
  simp at h_hom
  exact (Functor.conj_eqToHom_iff_heq xh yh (congrArg F.obj hl) (congrArg G.obj hr)).mp h_hom

open Gpd

def Obj_Obj_Comp {C : Type u₁}{D : Type u₂}{E : Type u₃}[Category.{v₁} C][Category.{v₂} D][Category.{v₃} E]
  (F: C ⥤ D)(G : D ⥤ E)(x : C): G.obj (F.obj x) = (F ⋙ G).obj x := by simp

namespace Functor

variable (G1 G2 : Type u) [Groupoid.{v} G1] [Groupoid.{v} G2] (F : G1 ⥤ G2)

def MiddleGroupoid : Groupoid.{v} (Comma F (Functor.id G2)) where
  inv f := CommaMorphism.mk (Groupoid.inv f.left) (Groupoid.inv f.right)


def Left_Functor : G1 ⥤ (Comma F (Functor.id G2)) where
  obj x := Comma.mk x (F.obj x) (𝟙 (F.obj x))
  map f := CommaMorphism.mk (f) (F.map f)

def mid (X : Diagrams.WalkingArrow ⥤ Gpd.{u}) : Gpd.{u} := ⟨(Comma (X.map Diagrams.WalkingArrowHom.morph) (Functor.id (X.obj Diagrams.WalkingArrow.one))), MiddleGroupoid (X.obj Diagrams.WalkingArrow.zero) (X.obj Diagrams.WalkingArrow.one) (X.map Diagrams.WalkingArrowHom.morph)⟩

@[simp] def Left_Morph (X : Diagrams.WalkingArrow ⥤ Gpd.{u}) : (X.obj Diagrams.WalkingArrow.zero) ⟶ (mid X) := (Left_Functor (X.obj Diagrams.WalkingArrow.zero) (X.obj Diagrams.WalkingArrow.one) (X.map Diagrams.WalkingArrowHom.morph))

def Right_Functor : (Comma F (Functor.id G2)) ⥤ G2 := CategoryTheory.Comma.snd F (Functor.id G2)

@[simp] def Right_Morph (X : Diagrams.WalkingArrow ⥤ Gpd) : (mid X) ⟶ (X.obj Diagrams.WalkingArrow.one) := (Right_Functor (X.obj Diagrams.WalkingArrow.zero) (X.obj Diagrams.WalkingArrow.one) (X.map Diagrams.WalkingArrowHom.morph))

theorem LR_comp : (Left_Functor G1 G2 F) ⋙ (Right_Functor G1 G2 F) = F := by
  simp [Functor.comp,Left_Functor,Right_Functor]

def FF_func_obj : (Diagrams.WalkingArrow ⥤ Gpd) → (Diagrams.WalkingTriangle ⥤ Gpd) := fun(X) => Diagrams.triangle (Left_Morph X) (Right_Morph X)

def Mid_func (X Y : Diagrams.WalkingArrow ⥤ Gpd.{u}) (η : NatTrans X Y) : (mid X) ⥤ (mid Y) := by
  unfold mid
  have eq2 := η.naturality (𝟙 Diagrams.WalkingArrow.one)
  rw [Functor.map_id Y,Functor.map_id X] at eq2
  exact @Comma.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (η.app (Diagrams.WalkingArrow.zero)) (η.app (Diagrams.WalkingArrow.one)) (η.app (Diagrams.WalkingArrow.one)) (eqToHom (η.naturality (Diagrams.WalkingArrowHom.morph)).symm) (eqToHom eq2)

def FF_func_map_app (X Y : Diagrams.WalkingArrow ⥤ Gpd.{u}) (η : NatTrans X Y) (t : Diagrams.WalkingTriangle) : (FF_func_obj X).obj t ⟶ (FF_func_obj Y).obj t := match t with
    | Diagrams.WalkingTriangle.zero => η.app Diagrams.WalkingArrow.zero
    | Diagrams.WalkingTriangle.two => η.app Diagrams.WalkingArrow.one
    | Diagrams.WalkingTriangle.one => Mid_func X Y η

theorem FF_func_map_Nat_left (X Y : Diagrams.WalkingArrow ⥤ Gpd.{u}) (η : NatTrans X Y) : X.FF_func_obj.map Diagrams.WalkingTriangleHom.left ≫ X.FF_func_map_app Y η Diagrams.WalkingTriangle.one =
  X.FF_func_map_app Y η Diagrams.WalkingTriangle.zero ≫ Y.FF_func_obj.map Diagrams.WalkingTriangleHom.left := by
    apply Functor.ext
    case h_obj;
    intro x
    simp [FF_func_map_app,Functor.comp,Comma.map,FF_func_obj,Left_Functor,Mid_func]
    apply Comma.ext <;> simp
    have N' :=  congr_obj (η.naturality (Diagrams.WalkingArrowHom.morph)) x
    simp only [CategoryStruct.comp,Functor.comp] at N'
    exact N'
    intro x y f
    simp [FF_func_map_app,FF_func_obj,Mid_func,Comma.map]
    congr
    rw [Comma.comp_left]
    simp[Left_Functor,Comma.left]
    rw [Comma.eqToHom_left,Comma.eqToHom_left]
    simp
    rw [Comma.comp_right]
    simp[Left_Functor,Comma.right]
    rw [Comma.eqToHom_right,Comma.eqToHom_right]
    have N' :=  congr_hom (η.naturality (Diagrams.WalkingArrowHom.morph)) f
    have map_comp_m : (X.map Diagrams.WalkingArrowHom.morph ≫ η.app Diagrams.WalkingArrow.one).map f = (η.app Diagrams.WalkingArrow.one).map ((X.map Diagrams.WalkingArrowHom.morph).map f) := by simp
    rw [<- map_comp_m, N']
    simp

theorem FF_func_map_Nat_right (X Y : Diagrams.WalkingArrow ⥤ Gpd.{u}) (η : NatTrans X Y) : X.FF_func_obj.map Diagrams.WalkingTriangleHom.right ≫ X.FF_func_map_app Y η Diagrams.WalkingTriangle.two =
  X.FF_func_map_app Y η Diagrams.WalkingTriangle.one ≫ Y.FF_func_obj.map Diagrams.WalkingTriangleHom.right := by
    simp [FF_func_obj,FF_func_map_app,Right_Morph,Right_Functor,Functor.comp]
    apply Functor.ext <;> simp [Functor.comp,Mid_func]

theorem FF_func_map_Nat_middle (X Y : Diagrams.WalkingArrow ⥤ Gpd.{u}) (η : NatTrans X Y) : X.FF_func_obj.map Diagrams.WalkingTriangleHom.middle ≫ X.FF_func_map_app Y η Diagrams.WalkingTriangle.two =
  X.FF_func_map_app Y η Diagrams.WalkingTriangle.zero ≫ Y.FF_func_obj.map Diagrams.WalkingTriangleHom.middle := by
    rw [<- Diagrams.LR_comp,Functor.map_comp,Category.assoc,FF_func_map_Nat_right,<- Category.assoc,FF_func_map_Nat_left]
    simp

def FF_func_map {X Y : Diagrams.WalkingArrow ⥤ Gpd.{u}} (η : NatTrans X Y) : NatTrans (FF_func_obj X) (FF_func_obj Y) where
  app := FF_func_map_app X Y η
  naturality T1 T2 f := by
    cases f
    exact FF_func_map_Nat_left X Y η
    exact FF_func_map_Nat_right X Y η
    exact FF_func_map_Nat_middle X Y η
    simp

def FF_func : (Diagrams.WalkingArrow ⥤ Gpd.{u}) ⥤ (Diagrams.WalkingTriangle ⥤ Gpd.{u}) where
  obj := FF_func_obj
  map := FF_func_map
  map_id X := by
    simp
    apply NatTrans.ext
    funext x
    cases x <;> simp [FF_func_map,FF_func_map_app,FF_func_obj]
    apply Functor.ext <;> simp[Mid_func,Comma.map]
    case app.h.one.h_obj;
    intro x
    apply Comma.ext <;> simp [CategoryStruct.id,Functor.id]
    intros A B h
    congr
    rw [Comma.comp_left]
    simp[Left_Functor,Comma.left]
    rw [Comma.eqToHom_left,Comma.eqToHom_left]
    simp
    rw [Comma.comp_right]
    simp[Left_Functor,Comma.right]
    rw [Comma.eqToHom_right,Comma.eqToHom_right]
    simp
  map_comp := by
    intros X Y Z f g
    apply NatTrans.ext
    funext x
    cases x <;> simp [FF_func_map,FF_func_map_app]
    apply Functor.ext <;> simp[Mid_func,Comma.map]
    intros A B h
    congr
    rw [Comma.comp_left]
    simp[Left_Functor,Comma.left]
    rw [Comma.eqToHom_left,Comma.eqToHom_left]
    simp
    rw [Comma.comp_right]
    simp[Left_Functor,Comma.right]
    rw [Comma.eqToHom_right,Comma.eqToHom_right]
    simp

instance Gpd_FF : FactFunc Gpd.{u} where
  func := FF_func
  cond := by
    apply Functor.ext <;> simp [Diagrams.PreCompMiddleFunctor,FF_func,Functor.comp]
    case h_obj;
    intro X
    apply Functor.ext
    case h_obj.h_obj;
    intro x
    cases x <;> simp [Diagrams.MiddleFunctor,FF_func_obj]
    intro x _ f
    cases f <;> simp [Diagrams.MiddleFunctor,FF_func_obj,CategoryStruct.comp]
    rw [LR_comp]
    simp [CategoryStruct.id,Functor.id,Functor.comp]
    apply Functor.ext <;> simp
    cases x <;> simp [CategoryStruct.id,Functor.comp_id]
    intros X Y f
    apply NatTrans.ext
    funext x
    cases x <;> simp[FF_func_map, FF_func_map_app,Diagrams.MiddleFunctor]


def Gpd_Mul : ((R Gpd_FF.{u}) ⋙ (R Gpd_FF.{u})) ⟶ (R Gpd_FF.{u}) := by
  apply NatTrans.mk
  case app;
  intro F
  apply NatTrans.mk
  case app.app;
  intro X
  cases X
  unfold R Gpd_FF FF_func FF_func_obj Diagrams.PreCompRightFunctor Diagrams.RightFunctor mid
  simp [MiddleGroupoid,Right_Functor,Quiver.Hom]
  sorry
  have eq1 : ((R Gpd_FF ⋙ R Gpd_FF).obj F).obj Diagrams.WalkingArrow.one = ((R Gpd_FF).obj F).obj Diagrams.WalkingArrow.one := by
    simp
  exact eqToHom eq1
  simp
  sorry
  sorry
