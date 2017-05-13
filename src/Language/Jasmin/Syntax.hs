{-# LANGUAGE FlexibleContexts, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric, DeriveFunctor #-}

module Language.Jasmin.Syntax where

import Text.PrettyPrint.Exts (Doc,PP(..),pp,(<>),(<+>),($+$),text,vcat,hcat,hsep,char)
import qualified Text.PrettyPrint.Exts as PP

import GHC.Generics (Generic,Generic1)
import Data.Generics hiding (Generic)
import Data.Binary
import Data.Bifunctor
import Data.Hashable.Exts
import Control.DeepSeq as DeepSeq
import Control.DeepSeq.Generics hiding (force)

import Control.Monad

import Language.Location
import Language.Vars
import Utils
import Data.Maybe

-- (* -------------------------------------------------------------------- *)
data Pident info = Pident info String
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pident info)
instance Hashable info => Hashable (Pident info)
instance NFData info => NFData (Pident info) where
    rnf = genericRnf
instance Monad m => PP m (Pident info) where
    pp (Pident _ n) = pp n
instance Location info => Located (Pident info) where
    type LocOf (Pident info) = info
    loc (Pident l _) = l
    updLoc (Pident _ x) l = Pident l x

type Piden = Pident ()

type Zint = Integer

-- (* -------------------------------------------------------------------- *)
data Peop1 = Not1
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Peop1
instance Hashable Peop1
instance NFData Peop1 where
    rnf = genericRnf
instance Monad m => PP m Peop1 where
    pp Not1 = return $ PP.char '!'

data Sign = Signed | Unsigned
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Sign
instance Hashable Sign
instance NFData Sign where
    rnf = genericRnf
instance Monad m => PP m Sign where
    pp Signed  = return $ PP.text "s"
    pp Unsigned  = return $ PP.empty

isNumericPeop2 Add2 = True
isNumericPeop2 Sub2 = True
isNumericPeop2 (Mul2) = True
isNumericPeop2 (Shr2 _) = True
isNumericPeop2 Shl2 = True
isNumericPeop2 BAnd2 = True
isNumericPeop2 BOr2 = True
isNumericPeop2 BXor2 = True
isNumericPeop2 _ = False

isBoolPeop2 And2 = True
isBoolPeop2 Or2 = True
isBoolPeop2 _ = False

isCmpPeop2 (Eq2)  = Just Unsigned
isCmpPeop2 (Neq2) = Just Unsigned
isCmpPeop2 (Lt2 s)  = Just s
isCmpPeop2 (Le2 s)  = Just s
isCmpPeop2 (Gt2 s)  = Just s
isCmpPeop2 (Ge2 s)  = Just s
isCmpPeop2 _ = Nothing

data Peop2 =
  Add2 | Sub2 | Mul2 | And2 | Or2  | BAnd2 | BOr2 | BXor2 |
  Shr2 Sign | Shl2 | Eq2 | Neq2 | Lt2 Sign | Le2 Sign | Gt2 Sign | Ge2 Sign
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Peop2
instance Hashable Peop2
instance NFData Peop2 where
    rnf = genericRnf
instance Monad m => PP m Peop2 where
    pp Add2  = return $ PP.text "+"
    pp Sub2  = return $ PP.text "-"
    pp (Mul2)  = do
        return $ PP.text "*"
    pp And2  = return $ PP.text "&&"
    pp Or2   = return $ PP.text "||"
    pp BAnd2 = return $ PP.text "&"
    pp BOr2  = return $ PP.text "|"
    pp BXor2 = return $ PP.text "^"
    pp (Shr2 s)  = do
        ps <- pp s
        return $ PP.text ">>" <> ps
    pp Shl2  = return $ PP.text "<<"
    pp (Eq2)   = do
        return $ PP.text "=="
    pp (Neq2)  = do
        return $ PP.text "!="
    pp (Lt2 s)  = do
        ps <- pp s
        return $ PP.text "<" <> ps
    pp (Le2  s)  = do
        ps <- pp s
        return $ PP.text "<=" <> ps
    pp (Gt2  s)  = do
        ps <- pp s
        return $ PP.text ">" <> ps
    pp (Ge2  s)  = do
        ps <- pp s
        return $ PP.text ">=" <> ps
    
data Quantifier
    = ForallQ
    | ExistsQ
  deriving (Show,Data,Typeable,Eq,Ord,Generic)

instance Binary (Quantifier)  
instance Hashable (Quantifier)
instance NFData Quantifier where
    rnf = genericRnf
instance Monad m => PP m (Quantifier) where
    pp (ForallQ) = return $ text "forall"
    pp (ExistsQ) = return $ text "exists"
    
-- (* -------------------------------------------------------------------- *)
data Pexpr_r info
  = PEParens [Pexpr info]
  | PEVar    (Pident info)
  | PEGet    (Pident info) (Pexpr info)
  | PEFetch  (Maybe (Ptype info)) (Pident info) (Pexpr info)
  | PEBool   Bool
  | Pcast    (Ptype info) (Pexpr info) -- internal
  | PEInt    Zint
  | PECall   (Pident info) [Pexpr info]
  | PEOp1    Peop1 (Pexpr info)
  | PEOp2    Peop2 (Pexpr info) (Pexpr info)
  -- annotations
  | LeakExpr (Pexpr info)
  | QuantifiedExpr Quantifier [Annarg info] (Pexpr info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pexpr_r info)
instance Hashable info => Hashable (Pexpr_r info)
instance NFData info => NFData (Pexpr_r info) where
    rnf = genericRnf
instance Monad m => PP m (Pexpr_r info) where
    pp (PEParens es) = do
        pes <- mapM pp es
        return $ PP.parens (PP.sepBy pes PP.comma)
    pp (PEVar v) = pp v
    pp (PEGet v e) = do
        pv <- pp v
        pe <- pp e
        return $ pv <> PP.brackets pe
    pp (PEFetch t v e) = do
        pt <- PP.ppOptM t $ \t -> pp t >>= \pt -> return $ PP.parens pt
        pv <- pp v
        pe <- pp e
        return $ pt <+> PP.brackets (pv <+> PP.char '+' <+> pe)
    pp (PEBool True) = return $ PP.text "true"
    pp (PEBool False) = return $ PP.text "false"
    pp (Pcast w e) = do
        pw <- pp w
        pe <- pp e
        return $ PP.parens pw <> pe
    pp (PEInt i) = return $ PP.integer i
    pp (PECall v es) = do
        pv <- pp v
        pes <- PP.sepByM (mapM pp es) PP.comma
        return $ pv <+> PP.parens pes
    pp (PEOp1 o e) = do
        po <- pp o
        pe <- pp e
        return $ po <> pe
    pp (PEOp2 o e1 e2) = do
        po <- pp o
        pe1 <- pp e1
        pe2 <- pp e2
        return $ pe1 <> po <> pe2
    pp (LeakExpr e) = do
        ppe <- pp e
        return $ text "public" <> PP.parens ppe
    pp (QuantifiedExpr q vs e) = do
        pq <- pp q
        pp1 <- mapM pp vs
        pp2 <- pp e
        return $ pq <+> PP.sepBy pp1 PP.comma <+> char ';' <+> pp2

-- (* -------------------------------------------------------------------- *)
data Wsize = W8 | W16 | W32 | W64 | W128 | W256
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Wsize
instance Hashable Wsize
instance NFData Wsize where
    rnf = genericRnf
instance Monad m => PP m Wsize where
    pp W8   = return $ PP.text "8"
    pp W16  = return $ PP.text "16"
    pp W32  = return $ PP.text "32"
    pp W64  = return $ PP.text "64"
    pp W128 = return $ PP.text "128"
    pp W256 = return $ PP.text "256"

wordSize :: Wsize -> Int
wordSize W8 = 8
wordSize W16 = 16
wordSize W32 = 32
wordSize W64 = 64
wordSize W128 = 128
wordSize W256 = 256

sizeWord :: Int -> Maybe Wsize
sizeWord 8   = Just W8
sizeWord 16  = Just W16
sizeWord 32  = Just W32
sizeWord 64  = Just W64
sizeWord 128 = Just W128
sizeWord 256 = Just W256
sizeWord n = Nothing

data Ptype info = TBool | TInt (Maybe Wsize) | TWord Wsize | TArray Wsize (Pexpr info)
    deriving (Data,Eq,Ord,Show,Typeable,Generic,Functor)
instance Binary info => Binary (Ptype info)
instance Hashable info => Hashable (Ptype info)
instance NFData info => NFData (Ptype info) where
    rnf = genericRnf
instance Monad m => PP m (Ptype info) where
    pp TBool = return $ PP.text "bool"
    pp (TInt Nothing) = return $ PP.text "int"
    pp (TInt (Just w)) = do
        pw <- pp w
        return $ PP.text "int" <> pw
    pp (TWord s) = do
        ps <- pp s
        return $ text "u" <> ps
    pp (TArray s e) = do
        ps <- pp s
        pe <- pp e
        return $ ps <> PP.brackets pe

wordTy (TWord w) = Just w
wordTy _ = Nothing

isBoolType TBool = True
isBoolType _ = False

isNumericType (TInt _) = True
isNumericType (TWord _) = True
isNumericType _ = False

type Pty = Ptype ()

-- (* -------------------------------------------------------------------- *)
data Pstorage = Reg | Stack | Inline
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Pstorage
instance Hashable Pstorage
instance NFData Pstorage where
    rnf = genericRnf
instance Monad m => PP m Pstorage where
    pp Reg = return $ PP.text "reg"
    pp Stack = return $ PP.text "stack"
    pp Inline = return $ PP.text "inline"

-- (* -------------------------------------------------------------------- *)
type Pstotype info = (Pstorage,Ptype info)

type Psoty = Pstotype ()

-- (* -------------------------------------------------------------------- *)
data Plvalue_r info
  = PLIgnore
  | PLVar   (Pident info)
  | PLArray (Pident info) (Pexpr info)
  | PLMem   (Maybe (Ptype info)) (Pident info) (Pexpr info)
  | PLParens [Plvalue info]
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Plvalue_r info)
instance Hashable info => Hashable (Plvalue_r info)
instance NFData info => NFData (Plvalue_r info) where
    rnf = genericRnf
instance Monad m => PP m (Plvalue_r info) where
    pp PLIgnore = return $ PP.char '_'
    pp (PLVar v) = pp v
    pp (PLArray v e) = do
        pv <- pp v
        pe <- pp e
        return $ pv <> PP.brackets pe
    pp (PLMem ct v e) = do
        pct <- PP.ppOptM ct $ \t -> pp t
        pv <- pp v
        pe <- pp e
        return $ pct <> PP.brackets (pv <+> PP.text "+" <+> pe) 
    pp (PLParens ps) = do
        pps <- mapM pp ps
        return $ PP.parens $ PP.sepBy pps PP.comma

type Plval = Plvalue ()

-- (* -------------------------------------------------------------------- *)
data Peqop = RawEq | AddEq | SubEq | ShREq | ShLEq | BAndEq | BXOrEq | BOrEq  | MulEq
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Peqop
instance Hashable Peqop
instance NFData Peqop where
    rnf = genericRnf
instance Monad m => PP m Peqop where
    pp RawEq = return $ PP.text "="
    pp AddEq = return $ PP.text "+="
    pp SubEq = return $ PP.text "-="
    pp ShREq = return $ PP.text ">>="
    pp ShLEq = return $ PP.text "<<="
    pp BAndEq = return $ PP.text "&="
    pp BXOrEq = return $ PP.text "^="
    pp BOrEq  = return $ PP.text "|="
    pp MulEq = return $ PP.text "*="

-- builtin operations (internal)
data Op = Oaddcarry | Osubcarry
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Op
instance Hashable Op
instance NFData Op where
    rnf = genericRnf
instance Monad m => PP m Op where
    pp Oaddcarry = return $ PP.text "#addcarry"
    pp Osubcarry = return $ PP.text "#subcarry"

-- (* -------------------------------------------------------------------- *)
data Pinstr_r info
  = PIAssign [Plvalue info] Peqop (Pexpr info) (Maybe (Pexpr info))
  | PIIf     Bool (Pexpr info) (Pblock info) (Maybe (Pblock info))
  | PIFor    (Pident info) Fordir (Pexpr info) (Pexpr info) [LoopAnnotation info] (Pblock info)
  | PIWhile  (Maybe (Pblock info)) (Pexpr info) [LoopAnnotation info] (Maybe (Pblock info))
  | Copn     [Plvalue info] Op [Pexpr info] -- internal
  | Ccall    [Plvalue info] (Pident info) [Pexpr info] -- internal
  | Anninstr (StatementAnnotation_r info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pinstr_r info)
instance Hashable info => Hashable (Pinstr_r info)
instance NFData info => NFData (Pinstr_r info) where
    rnf = genericRnf
ppQuestion Nothing doc = return doc
ppQuestion (Just v) doc = do
    pv <- pp v
    return $ pv <+> PP.char '?' <+> doc

instance Monad m => PP m (Pinstr_r info) where
    pp (PIAssign vs o e1 e2) = do
        pvs <- liftM PP.parens (PP.sepByM (mapM pp vs) PP.comma)
        po <- if null vs then return PP.empty else pp o
        pe1 <- pp e1
        pe2 <- PP.ppOptM e2 $ \x -> pp x >>= \px -> return $ PP.text "if" <+> px
        return $ pvs <+> po <+> pe1 <+> pe2 <> PP.semicolon
    pp (PIIf isPrivate e b1 b2) = do
        pe <- pp e
        pb1 <- pp b1
        pb2 <- PP.ppOptM b2 $ \x -> pp x >>= \px -> return $ PP.text "else" <+> px
        return $ PP.text "if" <+> pe <+> pb1 $+$ pb2
    pp (PIFor v e1 dir e2 anns b) = do
        pv <- pp v
        pe1 <- pp e1
        pdir <- pp dir
        pe2 <- pp e2
        panns <- pp anns
        pb <- pp b
        return $ PP.text "for" <+> pv <+> PP.text "=" <+> pe1 <+> pdir <+> pe2 $+$ panns $+$ pb
    pp (PIWhile b1 e anns b2) = do
        pe <- pp e
        panns <- pp anns
        pb1 <- PP.ppOptM b1 pp 
        pb2 <- PP.ppOptM b2 pp 
        return $ PP.text "while" <+> pb1 $+$ pe $+$ panns $+$ pb2
    pp (Copn ls o es) = do
        pls <- mapM pp ls
        po <- pp o
        pes <- mapM pp es
        return $ PP.parens (PP.sepBy pls PP.comma) <+> po <> PP.parens (PP.sepBy pes PP.comma)
    pp (Ccall ls n es) = do
        pls <- mapM pp ls
        pn <- pp n
        pes <- mapM pp es
        return $ PP.parens (PP.sepBy pls PP.comma) <+> PP.char '=' <+> pn <> PP.parens (PP.sepBy pes PP.comma)
    pp (Anninstr xs) = pp xs

data Fordir = Down | Up
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Fordir
instance Hashable Fordir
instance NFData Fordir where
    rnf = genericRnf
instance Monad m => PP m Fordir where
    pp Down = return $ PP.text "downto"
    pp Up = return $ PP.text "to"

type Pblock_r info = [Pinstr info]

-- (* -------------------------------------------------------------------- *)
data Pparam info = Pparam
    {  ppa_ty    :: Ptype info
    ,  ppa_name :: Pident info
    ,  ppa_init  :: Pexpr info
    }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pparam info)
instance Hashable info => Hashable (Pparam info)
instance NFData info => NFData (Pparam info) where
    rnf = genericRnf
instance Monad m => PP m (Pparam info) where
    pp (Pparam ty name init) = do
        pty <- pp ty
        pname <- pp name
        pinit <- pp init
        return $ PP.text "param" <+> pty <+> pname <+> PP.char '=' <+> pinit <> PP.semicolon
instance Location info => Located (Pparam info) where
    type LocOf (Pparam info) = info
    loc p = loc (ppa_name p)
    updLoc p l = p { ppa_name = updLoc (ppa_name p) l }

-- (* -------------------------------------------------------------------- *)
data Pfunbody info = Pfunbody
    {  pdb_vars  :: [Pbodyarg info]
    ,  pdb_instr :: [Pinstr info]
    ,  pdb_ret   :: Maybe [Pident info]
    }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pfunbody info)
instance Hashable info => Hashable (Pfunbody info)
instance NFData info => NFData (Pfunbody info) where
    rnf = genericRnf
instance Monad m => PP m (Pfunbody info) where
    pp (Pfunbody vars instr ret) = do
        vs <- mapM pp vars
        is <- mapM pp instr
        r <- PP.ppOptM ret $ \ret -> do
            vs <- PP.sepByM (mapM pp ret) PP.comma
            return $ PP.text "return" <+> PP.parens vs <> PP.semicolon
        return $ PP.vbraces $ PP.vcat vs $+$ PP.vcat is $+$ r

data Pcall_conv = CCExport | CCInline
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Pcall_conv
instance Hashable Pcall_conv
instance NFData Pcall_conv where
    rnf = genericRnf
instance Monad m => PP m Pcall_conv where
    pp CCExport = return $ PP.text "export"
    pp CCInline = return $ PP.text "inline"

-- (* -------------------------------------------------------------------- *)
data Pfundef info = Pfundef 
    {  pdf_cc   :: Maybe Pcall_conv
    ,  pdf_name :: Pident info
    ,  pdf_args :: [Parg info]
    ,  pdf_rty  :: Maybe [Pstotype info]
    ,  pdf_anns :: [ProcedureAnnotation info]
    ,  pdf_body :: Pfunbody info
    ,  pdf_info :: info
    }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pfundef info)
instance Hashable info => Hashable (Pfundef info)
instance NFData info => NFData (Pfundef info) where
    rnf = genericRnf

instance Monad m => PP m (Pfundef info) where
    pp (Pfundef cc name args ty anns body info) = do
        pcc <- PP.ppOptM cc pp
        n <- pp name
        as <- PP.parensM $ PP.sepByM (mapM pp args) (PP.text ",")
        t <- PP.ppOptM ty (\ty -> liftM (PP.text "->" <+>) (PP.sepByM (mapM PP.ppSpaced ty) (PP.text ",")))
        panns <- pp anns
        b <- pp body
        return $ pcc <+> PP.text "fn" <+> n <+> as <+> t $+$ panns $+$ b

instance Location info => Located (Pfundef info) where
    type LocOf (Pfundef info) = info
    loc f = pdf_info f
    updLoc f l = f { pdf_info = l }
    
data Parg info = Parg { pa_ty :: Pstotype info, pa_name :: Maybe (Pident info) }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Parg info)
instance Hashable info => Hashable (Parg info)
instance NFData info => NFData (Parg info) where
    
instance Monad m => PP m (Parg info) where
    pp (Parg ty n) = do
        pty <- pp ty
        pn <- pp n
        return $ pty <+> pn
    
data Pbodyarg info = Pbodyarg { pba_ty :: Pstotype info, pba_name :: Pident info }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pbodyarg info)
instance Hashable info => Hashable (Pbodyarg info)
instance NFData info => NFData (Pbodyarg info) where

instance Monad m => PP m (Pbodyarg info) where
    pp (Pbodyarg ty n) = do
        pty <- pp ty
        pn <- pp n
        return $ pty <+> pn <> PP.semicolon

data Annarg info = Annarg { aa_ty :: Ptype info, aa_name :: Pident info }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Annarg info)
instance Hashable info => Hashable (Annarg info)
instance NFData info => NFData (Annarg info) where
    
instance Monad m => PP m (Annarg info) where
    pp (Annarg ty n) = do
        pty <- pp ty
        pn <- pp n
        return $ pty <+> pn

-- (* -------------------------------------------------------------------- *)
data Pitem info
    = PFundef (Pfundef info)
    | PParam (Pparam info)
    | PAxiomdef (AnnAxiomDeclaration info)
    | PLemmadef (AnnLemmaDeclaration info)
    | PAnnfunctiondef (AnnFunDeclaration info)
  deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pitem info)
instance Hashable info => Hashable (Pitem info)
instance NFData info => NFData (Pitem info) where
    rnf = genericRnf
instance Monad m => PP m (Pitem info) where
    pp (PFundef d) = pp d
    pp (PParam p) = pp p
    pp (PAxiomdef x) = pp x
    pp (PLemmadef x) = pp x
    pp (PAnnfunctiondef x) = pp x

instance Location info => Located (Pitem info) where
    type LocOf (Pitem info) = info
    loc (PParam x) = loc x
    loc (PFundef x) = loc x
    loc (PAxiomdef x) = loc x
    loc (PLemmadef x) = loc x
    loc (PAnnfunctiondef x) = loc x
    updLoc (PParam x) l = PParam $ updLoc x l
    updLoc (PFundef x) l = PFundef $ updLoc x l
    updLoc (PAxiomdef x) l = PAxiomdef $ updLoc x l
    updLoc (PLemmadef x) l = PLemmadef $ updLoc x l
    updLoc (PAnnfunctiondef x) l = PAnnfunctiondef $ updLoc x l

-- (* -------------------------------------------------------------------- *)
newtype Pprogram info = Pprogram [Pitem info]
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pprogram info)
instance Hashable info => Hashable (Pprogram info)
instance NFData info => NFData (Pprogram info) where
    rnf = genericRnf

instance Monad m => PP m (Pprogram info) where
    pp (Pprogram xs) = do
        pxs <- mapM pp xs
        return $ PP.vcat pxs

instance Location info => Located (Pprogram info) where
    type LocOf (Pprogram info) = info
    loc (Pprogram []) = noloc
    loc (Pprogram (x:xs)) = loc x
    updLoc (Pprogram []) l = Pprogram []
    updLoc (Pprogram (x:xs)) l = Pprogram $ updLoc x l : xs

varPexpr :: Pident info -> Pexpr info
varPexpr v@(Pident l n) = (Pexpr l $ PEVar v)
varPlvalue :: Pident info -> Plvalue info
varPlvalue v@(Pident l n) = (Plvalue l $ PLVar v)

expr_of_lvalue :: Plvalue info -> Maybe (Pexpr info)
expr_of_lvalue (Plvalue l v) = case v of
    (PLVar x) -> Just $ Pexpr l $ PEVar x
    (PLArray v i) -> Just $ Pexpr l $ PEGet v i
    (PLMem ct v e) -> Just $ Pexpr l $ PEFetch ct v e
    PLParens es -> do
        es' <- mapM expr_of_lvalue es
        return $ Pexpr l $ PEParens es'
    PLIgnore -> Nothing

-- * annotations

data ProcedureAnnotation_r info
    = RequiresAnn Bool Bool (Pexpr info)
    | EnsuresAnn Bool Bool (Pexpr info)
    | PDecreasesAnn (Pexpr info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)

instance (Binary info) => Binary (ProcedureAnnotation_r info)  
instance (Hashable info) => Hashable (ProcedureAnnotation_r info)
instance NFData info => NFData (ProcedureAnnotation_r info) where
    rnf = genericRnf

instance Monad m => PP m (ProcedureAnnotation_r info) where
    pp (RequiresAnn isFree isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree isFree $ ppLeak isLeak $ text "requires" <+> ppe <> PP.semicolon
    pp (PDecreasesAnn e) = do
        ppe <- pp e
        return $ ppAnn $ text "decreases" <+> ppe <> PP.semicolon
    pp (EnsuresAnn isFree isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree isFree $ ppLeak isLeak $ text "ensures" <+> ppe <> PP.semicolon

data LoopAnnotation_r info
    = LDecreasesAnn Bool (Pexpr info)
    | LInvariantAnn Bool Bool (Pexpr info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
  
instance (Binary info) => Binary (LoopAnnotation_r info)  
instance (Hashable info) => Hashable (LoopAnnotation_r info)
instance NFData info => NFData (LoopAnnotation_r info) where
    rnf = genericRnf

instance (Monad m) => PP m (LoopAnnotation_r info) where
    pp (LDecreasesAnn free e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree free $ text "decreases" <+> ppe <> PP.semicolon
    pp (LInvariantAnn free isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree free $ ppLeak isLeak $ text "invariant" <+> ppe <> PP.semicolon

data StatementAnnotation_r info
    = AssumeAnn Bool (Pexpr info)
    | AssertAnn Bool (Pexpr info)
    | EmbedAnn  Bool (Pinstr info)
    | VarDefAnn (Annarg info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)

instance (Binary info) => Binary (StatementAnnotation_r info)  
instance (Hashable info) => Hashable (StatementAnnotation_r info)
instance NFData info => NFData (StatementAnnotation_r info) where
    rnf = genericRnf

instance (Monad m) => PP m (StatementAnnotation_r info) where
    pp (AssumeAnn isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppLeak isLeak $ text "assume" <+> ppe <> PP.semicolon
    pp (AssertAnn isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppLeak isLeak $ text "assert" <+> ppe <> PP.semicolon
    pp (EmbedAnn isLeak s) = do
        pps <- pp s
        return $ ppAnns $ ppLeak isLeak pps
    pp (VarDefAnn x) = do
        px <- pp x
        return $ px <> PP.semicolon

data AnnLemmaDeclaration info = AnnLemmaDeclaration
    { lemma_leak :: Bool -- is leakage
    , lemma_name :: (Pident info)
    , lemma_args :: [Annarg info]
    , lemma_anns :: [ProcedureAnnotation info]
    , lemma_body :: (Maybe (Pblock info))
    , lemma_info :: info
    }
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)

instance (Binary info) => Binary (AnnLemmaDeclaration info)  
instance (Hashable info) => Hashable (AnnLemmaDeclaration info)
instance NFData info => NFData (AnnLemmaDeclaration info) where
    rnf = genericRnf

instance Location info => Located (AnnLemmaDeclaration info) where
    type LocOf (AnnLemmaDeclaration info) = info
    loc (AnnLemmaDeclaration _ _ _ _ _ l) = l
    updLoc (AnnLemmaDeclaration isLeak n x y z _) l = AnnLemmaDeclaration isLeak n x y z l

instance (Monad m) => PP m (AnnLemmaDeclaration info) where
    pp (AnnLemmaDeclaration isLeak n params anns body _) = do
        pp1 <- pp n
        pp3 <- mapM pp params
        pp4 <- pp anns
        pp5 <- PP.ppOptM body (\stmts -> do { x <- pp stmts; return $ PP.nest 4 x })
        return $ ppLeak isLeak (text "lemma" <+> pp1 <+> PP.parens (PP.sepBy pp3 PP.comma) $+$ pp4 $+$ pp5)

data AnnFunDeclaration info = AnnFunDeclaration
    { af_leak :: Bool -- is leakage
    , af_ty :: (Ptype info)
    , af_name :: (Pident info)
    , af_args :: [Annarg info]
    , af_anns :: [ProcedureAnnotation info]
    , af_body :: (Pexpr info)
    , af_info :: info
    }
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance (Binary info) => Binary (AnnFunDeclaration info)  
instance (Hashable info) => Hashable (AnnFunDeclaration info)
instance NFData info => NFData (AnnFunDeclaration info) where
    rnf = genericRnf

instance Location info => Located (AnnFunDeclaration info) where
    type LocOf (AnnFunDeclaration info) = info
    loc (AnnFunDeclaration _ _ _ _ _ _ l) = l
    updLoc (AnnFunDeclaration isLeak n x y z ss _) l = AnnFunDeclaration isLeak n x y z ss l

instance (Monad m) => PP m (AnnFunDeclaration info) where
    pp (AnnFunDeclaration isLeak ret proc params anns stmts _) = do
        ppr <- pp ret
        ppp <- pp proc
        pas <- mapM pp params
        p1 <- pp anns
        p2 <- pp stmts
        return $ ppLeak isLeak (text "function" <+> ppr <+> ppp <+> PP.parens (PP.sepBy pas PP.comma) $+$ p1 $+$ PP.braces (PP.nest 4 p2))

data AnnAxiomDeclaration info = AnnAxiomDeclaration
    { ax_leak :: Bool -- is leakage
    , ax_args :: [Annarg info]
    , ax_anns :: [ProcedureAnnotation info]
    , ax_info :: info
    }
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)

instance (Binary info) => Binary (AnnAxiomDeclaration info)  
instance (Hashable info) => Hashable (AnnAxiomDeclaration info)
instance NFData info => NFData (AnnAxiomDeclaration info) where
    rnf = genericRnf

instance Location info => Located (AnnAxiomDeclaration info) where
    type LocOf (AnnAxiomDeclaration info) = info
    loc (AnnAxiomDeclaration _ _ _ l) = l
    updLoc (AnnAxiomDeclaration isLeak x y _) l = AnnAxiomDeclaration isLeak x y l

instance (Monad m) => PP m (AnnAxiomDeclaration info) where
    pp (AnnAxiomDeclaration isLeak params anns _) = do
        pp2 <- mapM pp params
        pp3 <- pp anns
        return $ ppLeak isLeak (text "axiom" <+> PP.parens (PP.sepBy pp2 PP.comma) $+$ pp3 )

ppAnns doc = vcat $ map (\x -> text "//@" <+> text x) $ lines $ show doc
ppAnn doc = text "//@" <+> doc

ppFree isFree doc = if isFree then text "free" <+> doc else doc
ppLeak isLeak doc = if isLeak then text "leakage" <+> doc else doc

data Pexpr info = Pexpr info (Pexpr_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (Pexpr info)
instance Hashable info => Hashable (Pexpr info)
instance NFData info => NFData (Pexpr info) where
    rnf = genericRnf
instance Monad m => PP m (Pexpr info) where
    pp (Pexpr _ x) = pp x
instance Vars Piden m info => Vars Piden m (Pexpr info) where
    traverseVars f (Pexpr l x) = do
        l' <- f l
        x' <- f x
        return $ Pexpr l' x'
    substL (Pexpr l v) = substL v
    unSubstL (Pexpr l v) v' = liftM (Pexpr l) $ unSubstL v v'
instance Location info => Located (Pexpr info) where
    type LocOf (Pexpr info) = info
    loc (Pexpr l _) = l
    updLoc (Pexpr _ x) l = Pexpr l x

data Pinstr info = Pinstr info (Pinstr_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (Pinstr info)
instance Hashable info => Hashable (Pinstr info)
instance NFData info => NFData (Pinstr info) where
    rnf = genericRnf
instance Monad m => PP m (Pinstr info) where
    pp (Pinstr _ x) = pp x
instance Vars Piden m info => Vars Piden m (Pinstr info) where
    traverseVars f (Pinstr l x) = do
        l' <- f l
        x' <- f x
        return $ Pinstr l' x'
instance Location info => Located (Pinstr info) where
    type LocOf (Pinstr info) = info
    loc (Pinstr l _) = l
    updLoc (Pinstr _ x) l = Pinstr l x

data Pblock info = Pblock info (Pblock_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (Pblock info)
instance Hashable info => Hashable (Pblock info)
instance NFData info => NFData (Pblock info) where
    rnf = genericRnf
instance Monad m => PP m (Pblock info) where
    pp (Pblock l x) = liftM (PP.vbraces . PP.vcat) (mapM pp x)
instance Vars Piden m info => Vars Piden m (Pblock info) where
    traverseVars f (Pblock l x) = do
        l' <- f l
        x' <- f x
        return $ Pblock l' x'
instance Location info => Located (Pblock info) where
    type LocOf (Pblock info) = info
    loc (Pblock l _) = l
    updLoc (Pblock _ x) l = Pblock l x

data Plvalue info = Plvalue info (Plvalue_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (Plvalue info)
instance Hashable info => Hashable (Plvalue info)
instance NFData info => NFData (Plvalue info) where
    rnf = genericRnf
instance Monad m => PP m (Plvalue info) where
    pp (Plvalue _ x) = pp x
instance Vars Piden m info => Vars Piden m (Plvalue info) where
    traverseVars f (Plvalue l x) = do
        l' <- f l
        x' <- f x
        return $ Plvalue l' x'
    substL (Plvalue l v) = substL v
    unSubstL (Plvalue l v) v' = liftM (Plvalue l) $ unSubstL v v'
instance Location info => Located (Plvalue info) where
    type LocOf (Plvalue info) = info
    loc (Plvalue l _) = l
    updLoc (Plvalue _ x) l = Plvalue l x

data ProcedureAnnotation info = ProcedureAnnotation info (ProcedureAnnotation_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (ProcedureAnnotation info)
instance Hashable info => Hashable (ProcedureAnnotation info)
instance NFData info => NFData (ProcedureAnnotation info) where
    rnf = genericRnf
instance Monad m => PP m (ProcedureAnnotation info) where
    pp (ProcedureAnnotation _ x) = pp x
instance Vars Piden m info => Vars Piden m (ProcedureAnnotation info) where
    traverseVars f (ProcedureAnnotation l x) = do
        l' <- f l
        x' <- f x
        return $ ProcedureAnnotation l x'
instance Location info => Located (ProcedureAnnotation info) where
    type LocOf (ProcedureAnnotation info) = info
    loc (ProcedureAnnotation l _) = l
    updLoc (ProcedureAnnotation _ x) l = ProcedureAnnotation l x

data LoopAnnotation info = LoopAnnotation info (LoopAnnotation_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (LoopAnnotation info)
instance Hashable info => Hashable (LoopAnnotation info)
instance NFData info => NFData (LoopAnnotation info) where
    rnf = genericRnf
instance Monad m => PP m (LoopAnnotation info) where
    pp (LoopAnnotation _ x) = pp x
instance Vars Piden m info => Vars Piden m (LoopAnnotation info) where
    traverseVars f (LoopAnnotation l x) = do
        l' <- f l
        x' <- f x
        return $ LoopAnnotation l' x'
instance Location info => Located (LoopAnnotation info) where
    type LocOf (LoopAnnotation info) = info
    loc (LoopAnnotation l _) = l
    updLoc (LoopAnnotation _ x) l = LoopAnnotation l x

data StatementAnnotation info = StatementAnnotation info (StatementAnnotation_r info)
  deriving (Show,Data,Typeable,Eq,Ord,Generic,Functor)
instance Binary info => Binary (StatementAnnotation info)
instance Hashable info => Hashable (StatementAnnotation info)
instance NFData info => NFData (StatementAnnotation info) where
    rnf = genericRnf
instance Monad m => PP m (StatementAnnotation info) where
    pp (StatementAnnotation _ x) = pp x
instance Vars Piden m info => Vars Piden m (StatementAnnotation info) where
    traverseVars f (StatementAnnotation l x) = do
        l' <- f l
        x' <- f x
        return $ StatementAnnotation l' x'
instance Location info => Located (StatementAnnotation info) where
    type LocOf (StatementAnnotation info) = info
    loc (StatementAnnotation l _) = l
    updLoc (StatementAnnotation _ x) l = StatementAnnotation l x

-- * variables

instance (Vars Piden m info) => Vars Piden m (Parg info) where
    traverseVars f (Parg ty n) = do
        ty' <- f ty
        n' <- inLHS False $ f n
        return $ Parg ty' n'

instance (Vars Piden m info) => Vars Piden m (Annarg info) where
    traverseVars f (Annarg ty n) = do
        ty' <- f ty
        n' <- inLHS False $ f n
        return $ Annarg ty' n'
    
instance (Vars Piden m info) => Vars Piden m (Pbodyarg info) where
    traverseVars f (Pbodyarg ty n) = do
        ty' <- f ty
        n' <- inLHS False $ f n
        return $ Pbodyarg ty' n'
    
instance (Vars Piden m info) => Vars Piden m (Pprogram info) where
    traverseVars f (Pprogram x) = do
        x' <- mapM f x
        return $ Pprogram x'

instance (Vars Piden m info) => Vars Piden m (Pitem info) where
    traverseVars f (PFundef x) = liftM PFundef $ f x
    traverseVars f (PParam x) = liftM PParam $ f x
    traverseVars f (PAxiomdef x) = liftM PAxiomdef $ f x
    traverseVars f (PLemmadef x) = liftM PLemmadef $ f x
    traverseVars f (PAnnfunctiondef x) = liftM PAnnfunctiondef $ f x

instance (Vars Piden m info) => Vars Piden m (Pfundef info) where
    traverseVars f (Pfundef cc n args ret anns body i) = do
        cc' <- f cc
        n' <- inLHS True $ f n
        ret' <- f ret
        i' <- f i
        varsBlock $ do
            args' <- mapM f args
            anns' <- f anns
            body' <- f body
            return $ Pfundef cc' n' args' ret' anns' body' i'

instance (Vars Piden m info) => Vars Piden m (AnnLemmaDeclaration info) where
    traverseVars f (AnnLemmaDeclaration isLeak n params anns body i) = do
        isLeak' <- f isLeak
        n' <- inLHS True $ f n
        i' <- f i
        varsBlock $ do
            params' <- f params
            anns' <- f anns
            body' <- f body
            return (AnnLemmaDeclaration isLeak' n' params' anns' body' i')

instance (Vars Piden m info) => Vars Piden m (AnnFunDeclaration info) where
    traverseVars f (AnnFunDeclaration isLeak ret n params anns body i) = do
        isLeak' <- f isLeak
        ret' <- f ret
        n' <- inLHS True $ f n
        i' <- f i
        varsBlock $ do
            params' <- f params
            anns' <- f anns
            body' <- f body
            return (AnnFunDeclaration isLeak' ret' n' params' anns' body' i')

instance (Vars Piden m info) =>  Vars Piden m (AnnAxiomDeclaration info) where
    traverseVars f (AnnAxiomDeclaration isLeak params anns i) = do
        isLeak' <- f isLeak
        i' <- f i
        varsBlock $ do
            params' <- f params
            anns' <- f anns
            return (AnnAxiomDeclaration isLeak' params' anns' i')

instance (Vars Piden m info) => Vars Piden m (Pparam info) where
    traverseVars f (Pparam t n e) = do
        t' <- f t
        n' <- inLHS False $ f n
        e' <- f e
        return $ Pparam t' n' e'

instance (Vars Piden m info) => Vars Piden m (Pfunbody info) where
    traverseVars f (Pfunbody vs is ret) = varsBlock $ do
        vs' <- mapM f vs
        is' <- mapM f is
        ret' <- mapM (mapM f) ret
        return $ Pfunbody vs' is' ret'

instance (Vars Piden m info) => Vars Piden m (Pexpr_r info) where
    traverseVars f (PEParens e) = liftM PEParens $ f e
    traverseVars f (PEVar n) = liftM PEVar $ f n
    traverseVars f (PEGet n i) = do
        n' <- f n
        i' <- f i
        return $ PEGet n' i'
    traverseVars f (PEFetch t n i) = do
        t' <- f t
        n' <- f n
        i' <- f i
        return $ PEFetch t' n' i'
    traverseVars f (PEBool b) = do
        b' <- f b
        return $ PEBool b'
    traverseVars f (Pcast w e) = do
        w' <- f w
        e' <- f e
        return $ Pcast w' e'
    traverseVars f (PEInt i) = liftM PEInt $ f i
    traverseVars f (PECall n es) = do
        n' <- f n
        es' <- mapM f es
        return $ PECall n' es'
    traverseVars f (PEOp1 o e) = do
        o' <- f o
        e' <- f e
        return $ PEOp1 o' e'
    traverseVars f (PEOp2 o e1 e2) = do
        o' <- f o
        e1' <- f e1
        e2' <- f e2
        return $ PEOp2 o' e1' e2'
    traverseVars f (LeakExpr e) = do
        e' <- f e
        return $ LeakExpr e'
    traverseVars f (QuantifiedExpr q args e) = do
        q' <- f q
        args' <- mapM f args
        e' <- f e
        return $ QuantifiedExpr q' args' e'
    
    substL (PEVar v) = substL v
    substL e = return Nothing
    unSubstL (PEVar v) v' = liftM PEVar $ unSubstL v v'
    unSubstL e v' = return e
        
instance (Vars Piden m info) => Vars Piden m (Plvalue_r info) where
    traverseVars f PLIgnore = return PLIgnore
    traverseVars f (PLVar v) = liftM PLVar $ f v
    traverseVars f (PLArray v e) = do
        v' <- f v
        e' <- inRHS $ f e
        return $ PLArray v' e'
    traverseVars f (PLMem t v e) = do
        t' <- inRHS $ f t
        v' <- f v
        e' <- inRHS $ f e
        return $ PLMem t' v' e'
    traverseVars f (PLParens es) = do
        es' <- mapM f es
        return $ PLParens es'
    
    substL (PLVar v) = substL v
    substL e = return Nothing
    unSubstL (PLVar v) v' = liftM PLVar $ unSubstL v v'
    unSubstL l v' = return l

instance (Vars Piden m info) => Vars Piden m (Pinstr_r info) where
    traverseVars f (PIAssign ls o e c) = do
        ls' <- mapM f ls
        o' <- f o
        e' <- f e
        c' <- mapM f c
        return $ PIAssign ls' o' e' c'
    traverseVars f (PIIf isPrivate c s1 s2) = do
        isPrivate' <- f isPrivate
        c' <- f c
        s1' <- f s1
        s2' <- mapM f s2
        return $ PIIf isPrivate' c' s1' s2'
    traverseVars f (PIFor x d from to anns b) = varsBlock $ do
        x' <- f x
        d' <- f d
        from' <- f from
        to' <- f to
        anns' <- f anns
        b' <- f b
        return $ PIFor x' d' from' to' anns' b'
    traverseVars f (PIWhile b1 e anns b2) = do
        b1' <- mapM f b1
        e' <- f e
        anns' <- f anns
        b2' <- mapM f b2
        return $ PIWhile b1' e' anns' b2'
    traverseVars f (Copn ls o es) = do
        ls' <- mapM f ls
        o' <- f o
        es' <- mapM f es
        return $ Copn ls' o' es'
    traverseVars f (Ccall ls n es) = do
        ls' <- mapM f ls
        n' <- f n
        es' <- mapM f es
        return $ Ccall ls' n' es'
    traverseVars f (Anninstr xs) = do
        xs' <- f xs
        return $ Anninstr xs'

instance (Vars Piden m info) => Vars Piden m (Ptype info) where
    traverseVars f TBool = return TBool
    traverseVars f (TInt w) = do
        w' <- mapM f w
        return $ TInt w'
    traverseVars f (TWord w) = liftM TWord $ f w
    traverseVars f (TArray w e) = do
        w' <- f w
        e' <- f e
        return $ TArray w' e'

instance (Vars Piden m info) => Vars Piden m (ProcedureAnnotation_r info) where
    traverseVars f (RequiresAnn isFree isLeak e) = do
        isFree' <- f isFree
        isLeak' <- f isLeak
        e' <- f e
        return $ RequiresAnn isFree' isLeak' e'
    traverseVars f (PDecreasesAnn e) = do
        e' <- f e
        return $ PDecreasesAnn e'
    traverseVars f (EnsuresAnn isFree isLeak e) = do
        isFree' <- f isFree
        isLeak' <- f isLeak
        e' <- f e
        return $ EnsuresAnn isFree' isLeak' e'

instance (Vars Piden m info) => Vars Piden m (LoopAnnotation_r info) where
    traverseVars f (LDecreasesAnn isFree e) = do
        isFree' <- f isFree
        e' <- f e
        return $ LDecreasesAnn isFree' e'
    traverseVars f (LInvariantAnn isFree isLeak e) = do
        isFree' <- f isFree
        isLeak' <- f isLeak
        e' <- f e
        return $ LInvariantAnn isFree' isLeak' e'

instance (Vars Piden m info) => Vars Piden m (StatementAnnotation_r info) where
    traverseVars f (AssumeAnn isLeak e) = do
        isLeak' <- f isLeak
        e' <- f e
        return $ AssumeAnn isLeak' e'
    traverseVars f (AssertAnn isLeak e) = do
        isLeak' <- f isLeak
        e' <- f e
        return $ AssertAnn isLeak' e'
    traverseVars f (EmbedAnn isLeak e) = do
        isLeak' <- f isLeak
        e' <- f e
        return $ EmbedAnn isLeak' e'
    traverseVars f (VarDefAnn x) = do
        x' <- f x
        return $ VarDefAnn x

instance (Vars Piden m info) => Vars Piden m (Pident info) where
    traverseVars f v@(Pident i n) = do
        i' <- inRHS $ f i
        isLHS <- getLHS
        Pident _ n' <- if isJust isLHS then addBV id (funit v) else addFV id (funit v)
        return $ Pident i' n'
    substL v = return $ Just (funit v)
    unSubstL (Pident i oldn) (Pident _ newn) = return $ Pident i newn

instance GenVar Piden m => Vars Piden m Pcall_conv where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Fordir where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Pstorage where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Peqop where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Peop1 where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Peop2 where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Op where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Wsize where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Sign where
    traverseVars f = return
instance GenVar Piden m => Vars Piden m Quantifier where
    traverseVars f = return






    