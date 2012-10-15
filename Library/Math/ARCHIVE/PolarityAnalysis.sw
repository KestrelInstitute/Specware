(*  
                 Polarity/Monotonicity Analysis 
                   of First-Order Functions 
                  by Abstract Interpretation


  Task: given a function f, and a parameter parm of interest, and a
  first-order recursive definition of f, produce an abstraction of f
  into the polarity domain, and solve for the greatest fixpoint to
  find the polarity (or monotonicity) property of f relative to change
  in parm.

*)

spec
  %import math/polarity-algebra
  import PolarityAlgebra %trying this, but it doesn't solve the problems

  type Expression = 
         | Var String 
         | Fun String*(List Expression) 
         | ite Expression*Expression*Expression

  type Defn = String * Expression
  type Program = List Defn

  type PolarityExpression = 
         | Var String 
         | Pol Polarity*(List PolarityExpression) 
         | Meet PolarityExpression*PolarityExpression

  type PolarityDefn = String * PolarityExpression
  type AbstractDomain = List PolarityDefn

  def abstractProgram (prg:Program): AbstractDomain = 
        map abstractDefn prg

  def abstractDefn (d:Defn): PolarityDefn =
        ("pol" ^ d.1, abstractExpr d.2)

  def abstractExpr (e:Expression) : PolarityExpression =
        case e of
          | Fun(f,args) -> if primitive(f)
                            then Pol(pol(f), (map abstractExpr args))
                          else Var ("pol" ^ f)
          | Var varname -> bot
          | ite(p,t,e) -> Meet( abstractExpr t, abstractExpr e )
            
  op primitive: String -> Boolean  % f is not in defined names
  op pol: String -> Polarity       % returns the polarity of a function


end-spec 
