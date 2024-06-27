import AWFS.Arrows
import AWFS.Triangle
import Mathlib.CategoryTheory.Whiskering

namespace CategoryTheory.Diagrams

universe v v₂ u u₂

open WalkingTriangleHom
open WalkingArrowHom

variable {C : Type u} [Category.{v} C]

def MiddleFunctor : WalkingArrow ⥤ WalkingTriangle where
  obj x := match x with
    | WalkingArrow.zero => WalkingTriangle.zero
    | WalkingArrow.one => WalkingTriangle.two
  map f := match f with
    | WalkingArrowHom.id _ => WalkingTriangleHom.id _
    | morph => middle
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;> {dsimp; simp}

def LeftFunctor : WalkingArrow ⥤ WalkingTriangle where
  obj x := match x with
    | WalkingArrow.zero => WalkingTriangle.zero
    | WalkingArrow.one => WalkingTriangle.one
  map f := match f with
    | WalkingArrowHom.id _ => WalkingTriangleHom.id _
    | morph => left
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;> {dsimp; simp}

def RightFunctor : WalkingArrow ⥤ WalkingTriangle where
  obj x := match x with
    | WalkingArrow.zero => WalkingTriangle.one
    | WalkingArrow.one => WalkingTriangle.two
  map f := match f with
    | WalkingArrowHom.id _ => WalkingTriangleHom.id _
    | morph => right
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;> {dsimp; simp}

def Left_Down : NatTrans LeftFunctor MiddleFunctor where
  app X := by
    cases X <;> simp[LeftFunctor,MiddleFunctor]
    exact WalkingTriangleHom.id WalkingTriangle.zero
    exact WalkingTriangleHom.right
  naturality _ _ η := by
    cases η <;> simp [LeftFunctor,MiddleFunctor,LR_comp]

def Right_Up : NatTrans MiddleFunctor RightFunctor  where
  app X := by
    cases X <;> simp[RightFunctor,MiddleFunctor]
    exact WalkingTriangleHom.left
    exact WalkingTriangleHom.id WalkingTriangle.two
  naturality _ _ η := by
    cases η <;> simp [RightFunctor,MiddleFunctor,LR_comp]

def PreCompMiddleFunctor : (WalkingTriangle ⥤ C) ⥤ (WalkingArrow ⥤ C) :=
  ((whiskeringLeft WalkingArrow WalkingTriangle C).obj MiddleFunctor)

@[simp]
theorem PCMF_obj_zero (F : WalkingTriangle ⥤ C) : ((PreCompMiddleFunctor).obj F).obj WalkingArrow.zero = F.obj WalkingTriangle.zero := rfl

@[simp]
theorem PCMF_obj_one (F : WalkingTriangle ⥤ C) : ((PreCompMiddleFunctor).obj F).obj WalkingArrow.one = F.obj WalkingTriangle.two := rfl

@[simp]
theorem PCMF_map_morph (F : WalkingTriangle ⥤ C) : ((PreCompMiddleFunctor).obj F).map WalkingArrowHom.morph = F.map WalkingTriangleHom.middle := rfl

def PreCompLeftFunctor : (WalkingTriangle ⥤ C) ⥤  (WalkingArrow ⥤ C) :=
  ((whiskeringLeft WalkingArrow WalkingTriangle C).obj LeftFunctor)

@[simp]
theorem PCLF_obj_zero (F : WalkingTriangle ⥤ C) : ((PreCompLeftFunctor).obj F).obj WalkingArrow.zero = F.obj WalkingTriangle.zero := rfl

@[simp]
theorem PCLF_obj_one (F : WalkingTriangle ⥤ C) : ((PreCompLeftFunctor).obj F).obj WalkingArrow.one = F.obj WalkingTriangle.one := rfl

@[simp]
theorem PCLF_map_morph (F : WalkingTriangle ⥤ C) : ((PreCompLeftFunctor).obj F).map WalkingArrowHom.morph = F.map WalkingTriangleHom.left := rfl


def PreCompRightFunctor : (WalkingTriangle ⥤ C) ⥤  (WalkingArrow ⥤ C) :=
  ((whiskeringLeft WalkingArrow WalkingTriangle C).obj RightFunctor)

@[simp]
theorem PCRF_obj_zero (F : WalkingTriangle ⥤ C) : ((PreCompRightFunctor).obj F).obj WalkingArrow.zero = F.obj WalkingTriangle.one := rfl

@[simp]
theorem PCRF_obj_one (F : WalkingTriangle ⥤ C) : ((PreCompRightFunctor).obj F).obj WalkingArrow.one = F.obj WalkingTriangle.two := rfl

@[simp]
theorem PCRF_map_morph (F : WalkingTriangle ⥤ C) : ((PreCompRightFunctor).obj F).map WalkingArrowHom.morph = F.map WalkingTriangleHom.right := rfl



def NatTrans_PCMF_PCRF_obj (F : WalkingTriangle ⥤ C) : NatTrans (PreCompMiddleFunctor.obj F) (PreCompRightFunctor.obj F) where
  app X := by
    simp [PreCompMiddleFunctor,PreCompRightFunctor]
    exact F.map (Right_Up.app X)
  naturality := by
    intros X Y f
    simp [PreCompMiddleFunctor,PreCompRightFunctor]
    cases f <;> simp[MiddleFunctor,RightFunctor]
    rw [<- F.map_comp,<- F.map_comp,<- F.map_comp]
    simp [Right_Up]

def NatTrans_PCMF_PCRF : NatTrans (@PreCompMiddleFunctor C _) (@PreCompRightFunctor C _) := by
  simp [PreCompMiddleFunctor,PreCompRightFunctor]
  exact (whiskeringLeft WalkingArrow WalkingTriangle C).map Right_Up

def NatTrans_PCLF_PCMF_obj (F : WalkingTriangle ⥤ C) : NatTrans (PreCompLeftFunctor.obj F) (PreCompMiddleFunctor.obj F) where
  app X := by
    simp [PreCompMiddleFunctor,PreCompRightFunctor]
    exact F.map (Left_Down.app X)
  naturality := by
    intros X Y f
    simp [PreCompMiddleFunctor,PreCompLeftFunctor]
    cases f <;> simp[MiddleFunctor,RightFunctor]
    rw [<- F.map_comp,<- F.map_comp,<- F.map_comp]
    simp

def NatTrans_PCLF_PCMF : NatTrans (@PreCompLeftFunctor C _) (@PreCompMiddleFunctor C _) := by
  simp [PreCompMiddleFunctor,PreCompLeftFunctor]
  exact (whiskeringLeft WalkingArrow WalkingTriangle C).map Left_Down
