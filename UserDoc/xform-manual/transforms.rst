
Transformations
###############

.. todo:: 
   
   Garrin's notes on common transformations.


::

  C2 = transform C1 by {at (findDead,FI_loop),
                            simplify (unfold extract,
                                      unfold getHeap,
                                      unfold nextSet
                                      ),
                            AbstractCommonExprs}

::

  C4 = transform C3 by {isomorphism(iso0, osi0),
                        at addArc', 
                        lr Union_map_mapset_apply_over_update, 
                        simplify (lr union_over_set_insert, 
                                  lr set_diff_over_set_insert, 
                                  lr union_mapset)
                      }



:: 

  I1 = transform I1_pre by 
            {implement(initNodes,initNodes_def)
                      (rl L2C_Nil,
                       rl L2C_Cons,
                       ...)}


::

  C3 = transform C2 by {introduce(WS)(lr *.flatten_nested_conditional_1,
                                    lr *.flatten_nested_conditional_2,
                                    lr allSucs_of_addArc,
                                    lr allSucs_of_delArc,
                                    lr allSucs_of_addNew,
                                    lr allSucs_of_addSupply)
                    at insertBlack, 
                     move (n),   % (n, l), 
                     lr *.distribute_coll_join_over_diff, 
                     fold WS
                   } 

:: 

  I2 = transform I2_pre by 
            {implement(initNodes,initNodes_def)
                      (rl L2C_Nil,
                       rl L2C_Cons,
                       rl L2C_delete1, 
                       rl L2C_member, 
                       rl L2C_head,
                       rl L2C_tail,
                       rl L2C_concat,
                       rl L2C_diff,
                       rl L2C_map,
                       rl L2C_map_apply
                       )
                         } 


#. Simplify

#. unfold

#. fold


#. implement

#. AbstractCommonExprs

#. isomorphism


#. introduce
