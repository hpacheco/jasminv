{-# LANGUAGE FlexibleContexts, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric, DeriveFunctor #-}

module Language.Jasmin.Syntax where

import Text.PrettyPrint.Exts (Doc,PP(..),pp,(<>),(<+>),($+$))
import qualified Text.PrettyPrint.Exts as PP

import GHC.Generics (Generic)
import Data.Generics hiding (Generic)
import Data.Binary
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
    
data Peop2 =
  Add2 | Sub2 | Mul2 | And2 | Or2  | BAnd2 | BOr2 | BXor2 |
  Shr2 | Shl2 | Eq2  | Neq2 | Lt2  | Le2   | Gt2  | Ge2 
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Peop2
instance Hashable Peop2
instance NFData Peop2 where
    rnf = genericRnf
instance Monad m => PP m Peop2 where
    pp Add2  = return $ PP.text "+"
    pp Sub2  = return $ PP.text "-"
    pp Mul2  = return $ PP.text "*"
    pp And2  = return $ PP.text "&&"
    pp Or2   = return $ PP.text "||"
    pp BAnd2 = return $ PP.text "&"
    pp BOr2  = return $ PP.text "|"
    pp BXor2 = return $ PP.text "^"
    pp Shr2  = return $ PP.text ">>"
    pp Shl2  = return $ PP.text "<<"
    pp Eq2   = return $ PP.text "=="
    pp Neq2  = return $ PP.text "!="
    pp Lt2   = return $ PP.text "<"
    pp Le2   = return $ PP.text "<="
    pp Gt2   = return $ PP.text ">"
    pp Ge2   = return $ PP.text ">="
    
-- (* -------------------------------------------------------------------- *)
data Pexpr_r info
  = PEParens (Pexpr info)
  | PEVar    (Pident info)
  | PEGet    (Pident info) (Pexpr info)
  | PEFetch  (Maybe (Ptype info)) (Pident info) (Pexpr info)
  | PEBool   Bool
  | Pcast    Wsize (Pexpr info) -- internal
  | PEInt    Zint
  | PECall   (Pident info) [Pexpr info]
  | PEOp1    Peop1 (Pexpr info)
  | PEOp2    Peop2 (Pexpr info) (Pexpr info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pexpr_r info)
instance Hashable info => Hashable (Pexpr_r info)
instance NFData info => NFData (Pexpr_r info) where
    rnf = genericRnf
instance Monad m => PP m (Pexpr_r info) where
    pp (PEParens e) = PP.parensM (pp e)
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

data Pexpr info = Pexpr info (Pexpr_r info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pexpr info)
instance Hashable info => Hashable (Pexpr info)
instance NFData info => NFData (Pexpr info) where
    rnf = genericRnf
instance Monad m => PP m (Pexpr info) where
    pp (Pexpr _ n) = pp n
instance Location info => Located (Pexpr info) where
    type LocOf (Pexpr info) = info
    loc (Pexpr l _) = l
    updLoc (Pexpr _ x) l = Pexpr l x

-- (* -------------------------------------------------------------------- *)
data Wsize = W8 | W16 | W32 | W64 | W128 | W256
    deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Binary Wsize
instance Hashable Wsize
instance NFData Wsize where
    rnf = genericRnf
instance Monad m => PP m Wsize where
    pp W8   = return $ PP.text "u8"
    pp W16  = return $ PP.text "u16"
    pp W32  = return $ PP.text "u32"
    pp W64  = return $ PP.text "u64"
    pp W128 = return $ PP.text "u128"
    pp W256 = return $ PP.text "u256"

wordSize :: Wsize -> Int
wordSize W8 = 8
wordSize W16 = 16
wordSize W32 = 32
wordSize W64 = 64
wordSize W128 = 127
wordSize W256 = 256

data Ptype info = TBool | TInt | TWord Wsize | TArray Wsize (Pexpr info)
    deriving (Data,Eq,Ord,Show,Typeable,Generic,Functor)
instance Binary info => Binary (Ptype info)
instance Hashable info => Hashable (Ptype info)
instance NFData info => NFData (Ptype info) where
    rnf = genericRnf
instance Monad m => PP m (Ptype info) where
    pp TBool = return $ PP.text "bool"
    pp TInt = return $ PP.text "int"
    pp (TWord s) = pp s
    pp (TArray s e) = do
        ps <- pp s
        pe <- pp e
        return $ ps <> PP.brackets pe

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

type Plval = Plvalue ()

data Plvalue info = Plvalue info (Plvalue_r info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Plvalue info)
instance Hashable info => Hashable (Plvalue info)
instance NFData info => NFData (Plvalue info) where
    rnf = genericRnf
instance Monad m => PP m (Plvalue info) where
    pp (Plvalue _ n) = pp n
instance Location info => Located (Plvalue info) where
    type LocOf (Plvalue info) = info
    loc (Plvalue l _) = l
    updLoc (Plvalue _ x) l = Plvalue l x

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
  | PIIf     (Pexpr info) (Pblock info) (Maybe (Pblock info))
  | PIFor    (Pident info) Fordir (Pexpr info) (Pexpr info) (Pblock info)
  | PIWhile  (Maybe (Pblock info)) (Pexpr info) (Maybe (Pblock info))
  | Copn     [Plvalue info] Op [Pexpr info] -- internal
  | Ccall    [Plvalue info] (Pident info) [Pexpr info] -- internal
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
        po <- pp o
        pe1 <- pp e1
        pe2 <- PP.ppOptM e2 $ \x -> pp x >>= \px -> return $ PP.text "if" <+> px
        return $ pvs <+> po <+> pe1 <+> pe2 <> PP.semicolon
    pp (PIIf e b1 b2) = do
        pe <- pp e
        pb1 <- ppPblock b1
        pb2 <- PP.ppOptM b2 $ \x -> ppPblock x >>= \px -> return $ PP.text "else" <+> px
        return $ PP.text "if" <+> pe <+> pb1 $+$ pb2
    pp (PIFor v e1 dir e2 b) = do
        pv <- pp v
        pe1 <- pp e1
        pdir <- pp dir
        pe2 <- pp e2
        pb <- ppPblock b
        return $ PP.text "for" <+> pv <+> PP.text "=" <+> pe1 <+> pdir <+> pe2 $+$ pb
    pp (PIWhile b1 e b2) = do
        pe <- pp e
        pb1 <- PP.ppOptM b1 ppPblock 
        pb2 <- PP.ppOptM b2 ppPblock 
        return $ PP.text "while" <+> pb1 $+$ pe $+$ pb2
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

ppPblock :: Monad m => Pblock info -> m Doc
ppPblock (Pblock l x) = liftM (PP.vbraces . PP.vcat) (mapM pp x)

data Pinstr info = Pinstr info (Pinstr_r info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pinstr info)
instance Hashable info => Hashable (Pinstr info)
instance NFData info => NFData (Pinstr info) where
    rnf = genericRnf
instance Monad m => PP m (Pinstr info) where
    pp (Pinstr _ n) = pp n
instance Location info => Located (Pinstr info) where
    type LocOf (Pinstr info) = info
    loc (Pinstr l _) = l
    updLoc (Pinstr _ x) l = Pinstr l x

data Pblock info = Pblock info (Pblock_r info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pblock info)
instance Hashable info => Hashable (Pblock info)
instance NFData info => NFData (Pblock info) where
    rnf = genericRnf
instance Monad m => PP m (Pblock info) where
    pp (Pblock _ n) = pp n
instance Location info => Located (Pblock info) where
    type LocOf (Pblock info) = info
    loc (Pblock l _) = l
    updLoc (Pblock _ x) l = Pblock l x

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
        vs <- mapM (\v -> PP.suffix (PP.ppSpaced3 v) PP.semicolon) vars
        is <- mapM pp instr
        r <- PP.ppOptM ret $ \ret -> do
            vs <- PP.sepByM (mapM pp ret) PP.comma
            return $ PP.text "return" <+> PP.parens vs <> PP.semicolon
        return $ PP.vbraces $ PP.vcat vs $+$ PP.vcat is $+$ r

-- (* -------------------------------------------------------------------- *)
data Pfundef info = Pfundef 
    {  pdf_name :: Pident info
    ,  pdf_args :: [Parg info]
    ,  pdf_rty  :: Maybe [Pstotype info]
    ,  pdf_body :: Pfunbody info
    ,  pdf_info :: info
    }
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pfundef info)
instance Hashable info => Hashable (Pfundef info)
instance NFData info => NFData (Pfundef info) where
    rnf = genericRnf
type Parg info = (Pstotype info,Maybe (Pident info))
type Pbodyarg info = (Pstotype info,Pident info)

instance Monad m => PP m (Pfundef info) where
    pp (Pfundef name args ty body info) = do
        n <- pp name
        as <- PP.parensM (PP.sepByM (mapM PP.ppSpaced3 args) (PP.text ","))
        t <- PP.ppOptM ty (\ty -> liftM (PP.text "->" <+>) (PP.sepByM (mapM PP.ppSpaced ty) (PP.text ",")))
        b <- pp body
        return $ PP.text "fn" <+> n <+> as <+> t $+$ b

instance Location info => Located (Pfundef info) where
    type LocOf (Pfundef info) = info
    loc f = pdf_info f
    updLoc f l = f { pdf_info = l }

-- (* -------------------------------------------------------------------- *)
data Pitem info = PFundef (Pfundef info) | PParam (Pparam info)
    deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Binary info => Binary (Pitem info)
instance Hashable info => Hashable (Pitem info)
instance NFData info => NFData (Pitem info) where
    rnf = genericRnf
instance Monad m => PP m (Pitem info) where
    pp (PFundef d) = pp d
    pp (PParam p) = pp p

instance Location info => Located (Pitem info) where
    type LocOf (Pitem info) = info
    loc (PParam x) = loc x
    loc (PFundef x) = loc x
    updLoc (PParam x) l = PParam $ updLoc x l
    updLoc (PFundef x) l = PFundef $ updLoc x l

-- (* -------------------------------------------------------------------- *)
type Pprogram info = [Pitem info]

pprogramLoc :: Location info => Pprogram info -> info
pprogramLoc [] = noloc
pprogramLoc (x:xs) = loc x

ppPprogram :: Monad m => Pprogram info -> m Doc
ppPprogram xs = do
    pxs <- mapM pp xs
    return $ PP.vcat pxs

varPexpr :: Pident info -> Pexpr info
varPexpr v@(Pident l n) = (Pexpr l $ PEVar v)
varPlvalue :: Pident info -> Plvalue info
varPlvalue v@(Pident l n) = (Plvalue l $ PLVar v)

expr_of_lvalue :: Plvalue info -> Maybe (Pexpr info)
expr_of_lvalue (Plvalue l v) = case v of
    (PLVar x) -> Just $ Pexpr l $ PEVar x
    (PLArray v i) -> Just $ Pexpr l $ PEGet v i
    (PLMem ct v e) -> Just $ Pexpr l $ PEFetch ct v e
    PLIgnore -> Nothing

instance (Vars Piden m info) => Vars Piden m (Pitem info) where
    traverseVars f (PFundef x) = liftM PFundef $ f x
    traverseVars f (PParam x) = liftM PParam $ f x

instance (Vars Piden m info) => Vars Piden m (Pfundef info) where
    traverseVars f (Pfundef n args ret body i) = do
        n' <- inLHS True $ f n
        ret' <- f ret
        i' <- f i
        varsBlock $ do
            args' <- mapM f args
            body' <- f body
            return $ Pfundef n' args' ret' body' i'

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

instance (Vars Piden m info) => Vars Piden m (Pexpr info) where
    traverseVars f (Pexpr i e) = do
        i' <- f i
        e' <- f e
        return $ Pexpr i' e'

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
    
    substL (PEVar v) = substL v
    substL e = return Nothing
    unSubstL (PEVar v) v' = liftM PEVar $ unSubstL v v'
    unSubstL e v' = return e

instance (Vars Piden m info) => Vars Piden m (Plvalue info) where
    traverseVars f (Plvalue i e) = do
        i' <- inRHS $ f i
        e' <- inLVal $ f e
        return $ Plvalue i' e'
        
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
    
    substL (PLVar v) = substL v
    substL e = return Nothing
    unSubstL (PLVar v) v' = liftM PLVar $ unSubstL v v'
    unSubstL l v' = return l

instance (Vars Piden m info) => Vars Piden m (Pblock info) where
    traverseVars f (Pblock i e) = do
        i' <- f i
        e' <- mapM f e
        return $ Pblock i' e'

instance (Vars Piden m info) => Vars Piden m (Pinstr info) where
    traverseVars f (Pinstr i e) = do
        i' <- f i
        e' <- f e
        return $ Pinstr i' e'

instance (Vars Piden m info) => Vars Piden m (Pinstr_r info) where
    traverseVars f (PIAssign ls o e c) = do
        ls' <- mapM f ls
        o' <- f o
        e' <- f e
        c' <- mapM f c
        return $ PIAssign ls' o' e' c'
    traverseVars f (PIIf c s1 s2) = do
        c' <- f c
        s1' <- f s1
        s2' <- mapM f s2
        return $ PIIf c' s1' s2'
    traverseVars f (PIFor x d from to b) = varsBlock $ do
        x' <- f x
        d' <- f d
        from' <- f from
        to' <- f to
        b' <- f b
        return $ PIFor x' d' from' to' b'
    traverseVars f (PIWhile b1 e b2) = do
        b1' <- mapM f b2
        e' <- f e
        b2' <- mapM f b2
        return $ PIWhile b1 e b2
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

instance (Vars Piden m info) => Vars Piden m (Ptype info) where
    traverseVars f TBool = return TBool
    traverseVars f TInt = return TInt
    traverseVars f (TWord w) = liftM TWord $ f w
    traverseVars f (TArray w e) = do
        w' <- f w
        e' <- f e
        return $ TArray w' e'

instance (Vars Piden m info) => Vars Piden m (Pident info) where
    traverseVars f v@(Pident i n) = do
        i' <- inRHS $ f i
        isLHS <- getLHS
        Pident _ n' <- if isJust isLHS then addBV id (funit v) else addFV id (funit v)
        return $ Pident i' n'
    substL v = return $ Just (funit v)
    unSubstL (Pident i oldn) (Pident _ newn) = return $ Pident i newn

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