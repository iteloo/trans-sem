module Main

-- equiv to a sigma type with the identity family
-- [question] doable using record syntax?
-- [note] unused packaging of base-cats and expressions
data TLang : Type where
  MkTLang : (a : Type) -> (p : a) -> (a -> Type) -> TLang

BaseCat : TLang -> Type
BaseCat (MkTLang a _ _) = a

sentenceCat : (l : TLang) -> BaseCat l
sentenceCat (MkTLang _ p _) = p

Expr : (l : TLang) -> BaseCat l -> Type
Expr (MkTLang _ _ e) = e

Sentence : TLang -> Type
Sentence l = Expr l (sentenceCat l)

infixr 10 +>
data Span a = Base a | (+>) a a

data BaseA = S | NP | VP

data AExpr : BaseA -> Type where
  Np : String -> AExpr NP
  Vp : String -> AExpr VP
  Cl : AExpr NP -> AExpr VP -> AExpr S

Ta : TLang
Ta = MkTLang BaseA S AExpr

implementation Show (AExpr a) where
  show (Np np) = np
  show (Vp vp) = vp
  show (Cl np vp) = "(cl " ++ show np ++ " " ++ show vp ++ ")"

john : AExpr NP
john = Np "John"

eat : AExpr VP
eat = Vp "eat"

je : AExpr S
je = Cl john eat

data BaseL = T | E

data LExpr : BaseL -> Type where
  Entity : String -> LExpr E
  Property : String -> LExpr E -> LExpr T

TL : TLang
TL = MkTLang BaseL T LExpr

implementation Show (LExpr a) where
  show (Entity e) = e
  show (Property p e) = p ++ "(" ++ show e ++ ")"

data Transformer : TLang -> TLang -> Type where
  MkTransformer : {la : TLang} -> {lb : TLang}
              -> (Sentence la -> Sentence lb)
              -> Transformer la lb

infixl 1 >>>
(>>>) : Sentence la -> Transformer la lb -> Sentence lb
e >>> (MkTransformer t) = t e

baseMapAL : BaseA -> Span BaseL
baseMapAL S = Base T
baseMapAL NP = Base E
baseMapAL VP = E +> T

-- [note] looks like fold
infixr 9 /@
(/@) : (a -> Type) -> Span a -> Type
e /@ (Base a) = e a
e /@ (a +> b) = e a -> e b

transformAL : Transformer Ta TL
transformAL = MkTransformer subtrans
  where
    -- [note] looks like fold again
    subtrans : AExpr a -> LExpr /@ baseMapAL a
    subtrans (Np np) = Entity np
    subtrans (Vp vp) = Property vp
    subtrans (Cl np vp) = subtrans vp $ subtrans np

main : IO ()
main = print $ je >>> transformAL
