
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Data.Graph.MapGraph

import public Data.Graph

import Data.Map.AAMap

%default total
%access private

--}

--------------------------------------------------------------------------[ Graph as a Finite Map ]
--{1

||| Type defining a mapping between node id's and their context.
||| Pick your poison here.
NodeMap : Type -> Type
NodeMap = AAMap NodeId


||| Context variant that is the value of a NodeId mapping.
record MapContext a b where
  constructor MapCtx
  pred : Adj b
  node : a
  succ : Adj b

showMapCtx : (Show a, Show b) => NodeId -> MapContext a b -> String
showMapCtx n (MapCtx p v s) =
    let p_str = "Pred : " ++
                foldr (\(l,v), acc =>
                        (show v) <+> ":" <+> (show l) <+> " " <+> acc
                      ) "\n" p
        s_str = "Succ : " ++
                foldr (\(l,v), acc =>
                        (show v) <+> ":" <+> (show l) <+> " " <+> acc
                      ) "\n" s
        n_str = concat (the (List String) [ "Node : ", show n, ":", show v, "\n"])
    in concat (the (List String) [ n_str, p_str, s_str, "\n\n" ])



namespace Adj
  ||| Add to Adj Preds
  addPred : NodeId -> b -> MapContext a b -> MapContext a b
  addPred n l (MapCtx p v s) = MapCtx ((l,n)::p) v s

  ||| Add to Adj Succs
  addSucc : NodeId -> b -> MapContext a b -> MapContext a b
  addSucc n l (MapCtx p v s) = MapCtx p v ((l,n)::s)

  ||| Delete from Adj Preds
  delPred : NodeId -> b -> MapContext a b -> MapContext a b
  delPred n _ (MapCtx p v s) = MapCtx (filter ((/= n) . snd) p) v s

  ||| Delete from Adj Succs
  delSucc : NodeId -> b -> MapContext a b -> MapContext a b
  delSucc n _ (MapCtx p v s) = MapCtx p v (filter ((/= n) . snd) s)

  ||| Remove trivial (identity) loops from adjacency collection
  rmIdLoops : NodeId -> Adj b -> Adj b
  rmIdLoops n = filter ((/= n) . snd)

  ||| Update MapContext Adj's by a given function.
  updateAdj : Adj b
           -> (b -> MapContext a b -> MapContext a b)
           -> NodeMap (MapContext a b)
           -> NodeMap (MapContext a b)
  updateAdj adj f m = foldr (\(l,n), m' => case find n m of
                                             Nothing => m'
                                             Just v  => bind n (f l v) m'
                            ) m adj


||| Wrapper to use finite mappings as a Graph.
export
data MapGraph : Type -> Type -> Type where
  G : NodeMap (MapContext a b) -> MapGraph a b

export
(Show a, Show b) => Show (MapGraph a b) where
  show (G g) = let cs = cast {to=List (KVPair NodeId (MapContext a b))} g
               in concat $ map (\(KV k v) => showMapCtx k v) cs


||| Instance of a Graph using finite mappings.
public export
Graph MapGraph where
  empty          = G empty
  isEmpty  (G g) = isEmpty g
  nodeList (G g) = (\(KV k v) => MkNode k (node v)) <$> (cast g)

  mkGraph ns es  = assert_total $ addEdges es
                 $ G $ cast (map (\n => (uid n , MapCtx [] (ann n) [])) ns)

  match n (G g) with (find n g)
    | Nothing  = (Nothing , G g)
    | Just ctx = let p' = rmIdLoops n (pred ctx)     -- delete trivial loops in pred
                     s' = rmIdLoops n (succ ctx)     -- delete trivial loops in succ
                     g' = (updateAdj p' $ delSucc n) -- delete adj's using n as target
                        . (updateAdj s' $ delPred n) -- delete adj's using n as source
                        $ (delete n g)               -- remove the context node from g
                 in (Just (Ctx (pred ctx) (MkNode n (node ctx)) (succ ctx)) , G g')

  (&) (Ctx p n s) (G g) =
    G $ (updateAdj (rmIdLoops (uid n) p) $ addSucc (uid n)) -- update nodes with n as target
      . (updateAdj (rmIdLoops (uid n) s) $ addPred (uid n)) -- update nodes with n as source
      $ (bind (uid n) (MapCtx p (ann n) s) g)               -- bind the new context to g

--}


