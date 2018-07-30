
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Tests.MapGraph

import Testing.Unit

import Data.Graph.MapGraph

%default total
%access private

--}

---------------------------------------------------------------------------------[ Creation Tests ]
--{1

--{2 Common

||| Test graph provided in Erwig's paper.
g1 : MapGraph Char String
g1 = mkGraph [ MkNode 1 'a'
             , MkNode 2 'b'
             , MkNode 3 'c'
             ]
             [ MkEdge 1 2 "right"
             , MkEdge 2 1 "left"
             , MkEdge 2 3 "down"
             , MkEdge 3 1 "up"
             ]


||| String representation of g1.
g1_str : String
g1_str = "Node : 1:'a'\n"
      ++ "Pred : 2:\"left\" 3:\"up\" \n"
      ++ "Succ : 2:\"right\" \n"
      ++ "\n\n"
      ++ "Node : 2:'b'\n"
      ++ "Pred : 1:\"right\" \n"
      ++ "Succ : 1:\"left\" 3:\"down\" \n"
      ++ "\n\n"
      ++ "Node : 3:'c'\n"
      ++ "Pred : 2:\"down\" \n"
      ++ "Succ : 1:\"up\" \n"
      ++ "\n\n"

--}

--{2 T1

export
t_mkGraph : IO ()
t_mkGraph = assertEq "MG-Test 1 : Graph creation"
                     (show g1)
                     g1_str

--}

--{2 T2

export
t_Context : IO ()
t_Context = assertEq "MG-Test 2 : Adding a context"
                     (show $ (Ctx [("down",2)] (MkNode 3 'c') [("up",1)]) & g)
                     expect
  where
    g : MapGraph Char String
    g = mkGraph [ MkNode 1 'a'
                , MkNode 2 'b'
                ]
                [ MkEdge 1 2 "right"
                , MkEdge 2 1 "left"
                ]
    expect : String
    expect = "Node : 1:'a'\n"
          ++ "Pred : 3:\"up\" 2:\"left\" \n"
          ++ "Succ : 2:\"right\" \n"
          ++ "\n\n"
          ++ "Node : 2:'b'\n"
          ++ "Pred : 1:\"right\" \n"
          ++ "Succ : 3:\"down\" 1:\"left\" \n"
          ++ "\n\n"
          ++ "Node : 3:'c'\n"
          ++ "Pred : 2:\"down\" \n"
          ++ "Succ : 1:\"up\" \n"
          ++ "\n\n"

--}

--{2 T3

export
t_Decomp : IO ()
t_Decomp = assertEq "MG-Test 3 : Graph decomposition"
                    (show $ match 1 g1)
                    expect
  where
    expect : String
    expect = "(Just Node : 1:'a'\n"
          ++ "Pred : 2:\"left\" 3:\"up\" \n"
          ++ "Succ : 2:\"right\" \n"
          ++ "\n\n, "
          ++ "Node : 2:'b'\n"
          ++ "Pred : \n"
          ++ "Succ : 3:\"down\" \n"
          ++ "\n\n"
          ++ "Node : 3:'c'\n"
          ++ "Pred : 2:\"down\" \n"
          ++ "Succ : \n"
          ++ "\n\n)"
--}

--}

-----------------------------------------------------------------------------[ Modification Tests ]
--{1

--{2 T4

export
t_NodeAdd : IO ()
t_NodeAdd = assertEq "MG-Test 4 : Node Creation"
                    (show $ addNodes [MkNode 4 'd', MkNode 5 'e'] g1)
                    expect
  where
     expect : String
     expect = "Node : 1:'a'\n"
           ++ "Pred : 2:\"left\" 3:\"up\" \n"
           ++ "Succ : 2:\"right\" \n"
           ++ "\n\n"
           ++ "Node : 2:'b'\n"
           ++ "Pred : 1:\"right\" \n"
           ++ "Succ : 1:\"left\" 3:\"down\" \n"
           ++ "\n\n"
           ++ "Node : 3:'c'\n"
           ++ "Pred : 2:\"down\" \n"
           ++ "Succ : 1:\"up\" \n"
           ++ "\n\n"
           ++ "Node : 4:'d'\n"
           ++ "Pred : \n"
           ++ "Succ : \n"
           ++ "\n\n"
           ++ "Node : 5:'e'\n"
           ++ "Pred : \n"
           ++ "Succ : \n"
           ++ "\n\n"

--}

--{2 T5

export
t_NodeDel : IO ()
t_NodeDel = assertEq "MG-Test 5 : Node Deletion"
                    (show $ delNodes [1,2] $ (Ctx [("from_1",1)] (MkNode 4 'd') [("to_3",3)]) & g1)
                    expect
  where
     expect : String
     expect = "Node : 3:'c'\n"
           ++ "Pred : 4:\"to_3\" \n"
           ++ "Succ : \n"
           ++ "\n\n"
           ++ "Node : 4:'d'\n"
           ++ "Pred : \n"
           ++ "Succ : 3:\"to_3\" \n"
           ++ "\n\n"

--}

--{2 T6

export
t_EdgeAdd : IO ()
t_EdgeAdd = assertEq "MG-Test 6 : Adding Edges"
                    (show $ addEdges [ MkEdge 1 3 "e1"
                                     , MkEdge 3 2 "e2"] g1)
                    expect
  where
     expect : String
     expect = "Node : 1:'a'\n"
           ++ "Pred : 3:\"up\" 2:\"left\" \n"
           ++ "Succ : 3:\"e1\" 2:\"right\" \n"
           ++ "\n\n"
           ++ "Node : 2:'b'\n"
           ++ "Pred : 1:\"right\" 3:\"e2\" \n"
           ++ "Succ : 1:\"left\" 3:\"down\" \n"
           ++ "\n\n"
           ++ "Node : 3:'c'\n"
           ++ "Pred : 1:\"e1\" 2:\"down\" \n"
           ++ "Succ : 1:\"up\" 2:\"e2\" \n"
           ++ "\n\n"


--}

--{2 T6

export
t_EdgeDel : IO ()
t_EdgeDel = assertEq "MG-Test 7 : Delete Edges"
                     (show $ delEdges [ MkEdge 1 2 "right"
                                      , MkEdge 3 1 "up"
                                      ] g1)
                     expect
  where
     expect : String
     expect = "Node : 1:'a'\n"
           ++ "Pred : 2:\"left\" \n"
           ++ "Succ : \n"
           ++ "\n\n"
           ++ "Node : 2:'b'\n"
           ++ "Pred : \n"
           ++ "Succ : 1:\"left\" 3:\"down\" \n"
           ++ "\n\n"
           ++ "Node : 3:'c'\n"
           ++ "Pred : 2:\"down\" \n"
           ++ "Succ : \n"
           ++ "\n\n"

--}

--}



