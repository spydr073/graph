
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module DeBruijn

import Data.Graph
import Data.Graph.MapGraph

import Data.Tree.AA

import Data.Map.AAMap

%default total
%access private

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| A drop-in type alias for Sets.
Set : Type -> Type
Set = AATree


||| Get all kmer adjacencies from sequence.
kMerAdjs : Nat -> String -> List (String, String)
kMerAdjs k str = go (k+1) (unpack str) []
  where
    go : Nat -> List Char -> List (String, String) -> List (String, String)
    go k cs adjs with (nonEmpty cs)
      | No _   = []
      | Yes p1 = let seq = take k cs
                 in case nonEmpty seq of
                      No  _   => []
                      Yes p1 => case (length cs) < k of
                                   True  => adjs
                                   False => let mEdge = ( pack $ init seq
                                                        , pack $ tail seq)
                                            in go k (assert_smaller cs (tail cs))
                                                    (mEdge :: adjs)


||| Create a mapping between kmer strings and node uid's.
nodeMapping : List (String, String) -> AAMap String Integer
nodeMapping adjs = go adjs 0 empty
  where
    go : List (String, String) -> Integer -> AAMap String Integer -> AAMap String Integer
    go []            _   m = m
    go ((n1,n2)::es) uid m =
      case (find n1 m , find n2 m) of
        (Nothing, Nothing) => go es (uid+2) $ bind n2 (uid+1) $ bind n1 uid m
        (Just n1, Nothing) => go es (uid+1) $ bind n2 uid m
        (Nothing, Just n2) => go es (uid+1) $ bind n1 uid m
        (Just n1, Just n2) => go es  uid      m


||| Make a list of all kmer nodes from the sequence.
mkNodes : List (KVPair String Integer) -> List (Node String)
mkNodes = map (\(KV k v) => MkNode v k)


||| Make a list of all kmer edges from the sequence.
mkEdges : AAMap String Integer -> List (String, String) -> List (Edge ())
mkEdges m = foldr (\(n1,n2), acc =>
                      case (find n1 m, find n2 m) of
                        (Just uid1 , Just uid2) => (MkEdge uid1 uid2 ()) :: acc
                        (_         , _        ) => acc
                  ) []


||| Create a de bruijn graph of kmers from a given string.
export
mkDeBruijn : (Graph g) => Nat -> String -> g String ()
mkDeBruijn k str = let adjs    = kMerAdjs k str
                       nodeMap = nodeMapping adjs
                       ns      = mkNodes (cast nodeMap)
                       es      = mkEdges nodeMap adjs
                   in mkGraph ns es

--}


