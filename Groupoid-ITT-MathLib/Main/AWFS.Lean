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

def FF_Unit (FF : @FactorizationFunctor C _) : NatTrans (Functor.id (WalkingArrow ⥤ C)) (FF.func ⋙ PreCompRightFunctor) := by
  rw [<- FF.cond]
  apply NatTrans.hcomp (NatTrans.id FF.func)
  simp [Quiver.Hom]
  exact (@NatTrans_PCMF_PCRF C _)

def FF_CoUnit (FF : @FactorizationFunctor C _) : NatTrans (FF.func ⋙ PreCompLeftFunctor) (Functor.id (WalkingArrow ⥤ C)) := by
  rw [<- FF.cond]
  apply NatTrans.hcomp (NatTrans.id FF.func)
  simp [Quiver.Hom]
  exact (@NatTrans_PCLF_PCMF C _)
