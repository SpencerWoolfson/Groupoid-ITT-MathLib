import Main.TAFunctors

open CategoryTheory
open Diagrams
open WalkingTriangle
open WalkingArrow
open WalkingTriangleHom
open WalkingArrowHom

universe v v₂ u u₂
variable {C : Type u} [Category.{v} C]

structure FactorizationFunctor where
  func : (WalkingArrow ⥤ C) ⥤ (WalkingTriangle ⥤ C)
  cond : func ⋙ PreCompMiddleFunctor = Functor.id (WalkingArrow ⥤ C)

def FF_Unit (FF : @FactorizationFunctor C _) : NatTrans (Functor.id (WalkingArrow ⥤ C)) (FF.func ⋙ PreCompRightFunctor) where
  app F := by
    rw [<- FF.cond]
    simp
    exact NatTrans_PCMF_PCRF (FF.func.obj F)
  naturality := by
    intros F G η




    simp
