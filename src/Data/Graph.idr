
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Data.Graph

%default total
%access private

--}

----------------------------------------------------------------------------------[ Idris Prelude ]
--{1

--Uninhabited (True = False) where
--  uninhabited Refl impossible
--
--Uninhabited (False = True) where
--  uninhabited Refl impossible

infixl 9 ...
(...) : (c -> d) -> (a -> b -> c) -> a -> b -> d
(...) = (.) . (.)

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

--{2 Vertex

||| Unlabeled Vertex
public export
NodeId : Type
NodeId = Integer

||| Annotated Vertex
public export
record Node a where
  constructor MkNode
  uid : NodeId
  ann : a

||| Quasi-Labeled Vertex
public export
UNode : Type
UNode = Node ()

--}

--{2 Edge

-- ||| Unlabeled Edge
public export
EdgeId : Type
EdgeId = (NodeId, NodeId)

||| Annotated Edge
public export
record Edge a where
  constructor MkEdge
  start : NodeId
  end   : NodeId
  ann   : a

||| Quasi-Labeled Edge
public export
UEdge : Type
UEdge = Edge ()

--}

--{2 Context

||| List of edge annotations and the nodeId that they lead to.
public export
Adj : Type -> Type
Adj b = List (b, NodeId)

public export
record Context a b where
  constructor Ctx
  pred : Adj b
  node : Node a
  succ : Adj b

public export
Decomp : (Type -> Type -> Type) -> Type -> Type -> Type
Decomp g a b = (Maybe (Context a b), g a b)

public export
GDecomp : (Type -> Type -> Type) -> Type -> Type -> Type
GDecomp g a b = ((Context a b), g a b)

public export
UContext : Type
UContext = (List NodeId, NodeId, List NodeId)

public export
UDecomp : Type -> Type
UDecomp g = (Maybe UContext, g)

--}

--{2 Graph Interface

infixr 7 &

public export
interface Graph (g : Type -> Type -> Type) where
  empty    : g a b
  isEmpty  : g a b -> Bool
  nodeList : g a b -> List (Node a)
  match    : NodeId -> g a b -> Decomp g a b
  mkGraph  : List (Node a) -> List (Edge b) -> g a b
  (&)      : Context a b -> g a b -> g a b

--}

--{2 Unconditional Decomposition

export
matchAny : (Graph g) => (gr : g a b)
                     -> {default (nodeList gr) xs : List (Node a)}
                     -> {auto p : NonEmpty xs}
                     -> GDecomp g a b
matchAny g {xs} {p} with (xs)
  | []      = absurd p
  | (n::ns) = assert_total $ let ((Just c), g') = match (uid n) g
                             in (c, g')

--}

--}

--------------------------------------------------------------------------------------------[ API ]
--{1

--{2 Graph Traversal

||| Fold a function over the 'Contexts' of a graph.
ufold : (Graph g) => (Context a b -> c -> c) -> c -> g a b -> c
ufold f u g with (nodeList g)
  | []      = u
  | (n::ns) = let (c, g') = matchAny g {xs=(n::ns)}
              in f c (ufold f u (assert_smaller g g'))

||| Map a function over the 'Contexts' of a graph.
gmap : (Graph g) => (Context a b -> Context c d) -> g a b -> g c d
gmap f = ufold (\ctx, gr => ((f ctx) & gr)) empty

||| Map a function over the 'Node' labels in a graph.
nmap : (Graph g) => (a -> c) -> g a b -> g c b
nmap f = gmap (\ctx => let Ctx p n s = ctx
                       in Ctx p (MkNode (uid n) (f $ ann n)) s)

||| Map a function over the 'Edge' labels in a graph.
emap : (Graph g) => (b -> c) -> g a b -> g a c
emap f = gmap (\ctx => let Ctx p n s = ctx
                       in Ctx (map (\e => ((f $ fst e), (snd e))) p)
                              n
                              (map (\e => ((f $ fst e), (snd e))) s))

||| Map functions over both the 'Node' and 'Edge' labels in a graph.
nemap : (Graph gr) => (a -> c) -> (b -> d) -> gr a b -> gr c d
nemap fn fe = gmap (\(Ctx p n s) => Ctx (map (\e => (fe (fst e), snd e)) p)
                                        (MkNode (uid n) (fn $ ann n))
                                        (map (\e => (fe (fst e), snd e)) s))

--}

--{2 Graph Attributes

||| Get a list of all present edges in graph.
export
edgeList : Graph g => g a b -> List (Edge b)
edgeList = ufold (\ctx, es => let Ctx p n s = ctx
                              in map (\(l,w) => (MkEdge (uid n) w l)) s ++ es) []

||| Get the size of the graph, as the number of nodes.
export
order : (Graph g) => g a b -> Nat
order = length . nodeList

||| Get the size of the graph, as the number of edges.
export
size : (Graph g) => g a b -> Nat
size = length . edgeList

||| Drop the label component of an edge.
export
unlabelEdge : Edge b -> EdgeId
unlabelEdge (MkEdge v w _) = (v, w)

||| Label an edge.
export
labelEdge : EdgeId -> b -> Edge b
labelEdge (v, w) l = (MkEdge v w l)

||| Get the label of an edge.
export
edgeLabel : Edge b -> b
edgeLabel (MkEdge _ _ l) = l

||| List all 'Node' elements in the graph without labels.
export
nodes : (Graph g) => g a b -> List NodeId
nodes = map uid . nodeList

||| List all 'Edge' elements in the graph without labels.
export
edges : (Graph g) => g a b -> List EdgeId
edges = map unlabelEdge . edgeList

||| The minimum and maximum 'NodeId' in a graph.
export
nodeRange : (Graph g) => (gr : g a b)
                      -> {auto p : (isEmpty gr) ~=~ False}
                      -> (NodeId, NodeId)
nodeRange g {p} with (isEmpty g)
  | True  = absurd p
  | False = let vs = nodes g in (foldr min (pow 2 64) vs, foldr max 0 vs)

||| Check if a given NodeId is present in a graph
export
member : (Graph g) => NodeId -> g a b -> Bool
member v = isJust . fst . match v

--}

--{2 Graph Modification

||| Get a pool of available node uid's that are unassigned.
export
uidPool : (Graph g) => Integer -> g a b -> List NodeId
uidPool n g with (decEq (isEmpty g) False)
  | No  _   = [ 0 .. (n - 1) ]
  | Yes prf = let (_ , offset) = nodeRange g {p=prf}
              in [ (offset + 1) .. (offset + n) ]


||| Add a single node to a graph.
export
addNode : (Graph g) => Node a -> g a b -> g a b
addNode n = (&) (Ctx [] n [])


||| Add multiple nodes to a graph.
export
addNodes : (Graph g) => List (Node a) -> g a b -> g a b
addNodes ns g = foldr (\n,graph => addNode n graph) g ns


||| Add a single edge to a graph.
export
addEdge : (Graph g) => Edge b -> g a b -> g a b
addEdge (MkEdge u v b) g =
  case (member u g) && (member v g) of
    False => g
    True  => case match u g of
               (Nothing          , _ ) => g
               (Just $ Ctx p n s , g') => (Ctx p n ((b,v)::s)) & g'


||| Add multiple edges to a graph.
export
addEdges : (Graph g) => List (Edge b) -> g a b -> g a b
addEdges es g = foldr (\e, graph => addEdge e graph) g es


||| Delete a single node from a graph.
export
delNode : (Graph g) => NodeId -> g a b -> g a b
delNode n g with (match n g)
  | (Nothing , _ ) = g
  | (Just _  , g') = g'


||| Delete multiple nodes from a graph.
export
delNodes : (Graph g) => List NodeId -> g a b -> g a b
delNodes ns g = foldr (\n,graph => delNode n graph) g ns


||| Delete a single edge from a graph.
export
delEdge : (Graph g, Eq b) => Edge b -> g a b -> g a b
delEdge (MkEdge u v b) g with (match u g)
  | (Nothing          , _ ) = g
  | (Just (Ctx p n s) , g') = let f = (\e => (b /= fst e) || (v /= snd e))
                              in (Ctx p n (filter f s)) & g'


||| Delete multiple edges from a graph.
export
delEdges : (Graph g, Eq b) => List (Edge b) -> g a b -> g a b
delEdges es g = foldr (\e,graph => delEdge e graph) g es


--}

--{2 String Representation

||| Represent a Graph Context as a String.
export
(Show a, Show b) => Show (Context a b) where
  show (Ctx p n s) =
    let p_str = "Pred : " ++
                foldr (\(l,v), acc =>
                        (show v) <+> ":" <+> (show l) <+> " " <+> acc
                      ) "\n" p
        s_str = "Succ : " ++
                foldr (\(l,v), acc =>
                        (show v) <+> ":" <+> (show l) <+> " " <+> acc
                      ) "\n" s
        n_str = concat (the (List String) [ "Node : ", show (uid n), ":", show (ann n), "\n"])
    in concat (the (List String) [ n_str, p_str, s_str, "\n\n" ])

||| Represent an Inductive Graph as a String.
export
showGraph : (Graph gr, Show a, Show b) => gr a b -> String
showGraph g = ufold (\ctx, acc => (show ctx) <+> acc) "" g

--}

--}



