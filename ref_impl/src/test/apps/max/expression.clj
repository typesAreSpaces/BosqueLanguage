;; main.bsq
(assert 
    (and 
        (and 
            (= 
                __tmp_0 
                (>= NSMain__max__x NSMain__max__y)
            ) 
            MIRJumpCondFormula
        ) 
        (and
            (=>
                __tmp_0 
                (and 
                    (and 
                        (= NSMain__max___ir_ret_$1 NSMain__max__x) 
                        MIRJumpFormula) 
                    (and 
                        (and 
                            (=> 
                                __tmp_0 
                                (= NSMain__max___ir_ret_$2 NSMain__max___ir_ret_$1)
                            ) 
                            (=> 
                                (not __tmp_0) 
                                (= NSMain__max___ir_ret_$2 NSMain__max___ir_ret_)
                            )
                        ) 
                        (= NSMain__max___ir_ret_$2 NSMain__max___return_)
                    )
                )
            ) 
            (=> 
                (not __tmp_0) 
                (and 
                    (and 
                        (= NSMain__max___ir_ret_ NSMain__max__y) 
                        MIRJumpFormula
                    ) 
                    (and 
                        (and 
                            (=> 
                                __tmp_0 
                                (= NSMain__max___ir_ret_$2 NSMain__max___ir_ret_$1)
                            ) 
                            (=> 
                                (not __tmp_0) 
                                (= NSMain__max___ir_ret_$2 NSMain__max___ir_ret_)
                            )
                        ) 
                        (= 
                            NSMain__max___ir_ret_$2 
                            NSMain__max___return_
                        )
                    )
                )
            )
        )
    )
)

;; main2.bsq

(assert 
    (and 
        (and 
            (= 
                __tmp_0 
                (>= 
                    NSMain__max__x 
                    NSMain__max__y
                )
            ) 
            MIRJumpCondFormula
        ) 
        (and 
            (=> 
                __tmp_0 
                (and 
                    (and 
                        (= 
                            NSMain__max___ir_ret_$2 
                            NSMain__max__x
                        ) 
                        MIRJumpFormula
                    ) 
                    (and 
                        (and 
                            (and 
                                (=> 
                                    __tmp_0 
                                    (= 
                                        NSMain__max___ir_ret_$3 
                                        NSMain__max___ir_ret_$2
                                    )
                                ) 
                                (=> 
                                    __tmp_4 
                                    (= 
                                        NSMain__max___ir_ret_$3 
                                        NSMain__max___ir_ret_$1
                                    )
                                )
                            ) 
                            (=> 
                                (not 
                                    __tmp_4
                                ) 
                                (= 
                                    NSMain__max___ir_ret_$3 
                                    NSMain__max___ir_ret_
                                )
                            )
                        ) 
                        (= 
                            NSMain__max___ir_ret_$3 
                            NSMain__max___return_
                        )
                    )
                )
            ) 
            (=> 
                (not 
                    __tmp_0
                ) 
                (and 
                    (and 
                        (= 
                            __tmp_4 
                            (>= 
                                NSMain__max__x 0
                            )
                        ) 
                        MIRJumpCondFormula
                    ) 
                    (and 
                        (=> 
                            __tmp_4 
                            (and 
                                (and 
                                    (= 
                                        NSMain__max___ir_ret_$1 
                                        NSMain__max__y
                                    ) 
                                    MIRJumpFormula
                                ) 
                                (and 
                                    (and 
                                        (and 
                                            (=> 
                                                __tmp_0 
                                                (= 
                                                    NSMain__max___ir_ret_$3 
                                                    NSMain__max___ir_ret_$2
                                                )
                                            ) 
                                            (=> 
                                                __tmp_4 
                                                (= 
                                                    NSMain__max___ir_ret_$3 
                                                    NSMain__max___ir_ret_$1
                                                )
                                            )
                                        ) 
                                        (=> 
                                            (not 
                                                __tmp_4
                                            ) 
                                            (= 
                                                NSMain__max___ir_ret_$3 
                                                NSMain__max___ir_ret_
                                            )
                                        )
                                    ) 
                                    (= 
                                        NSMain__max___ir_ret_$3 
                                        NSMain__max___return_
                                    )
                                )
                            )
                        ) 
                        (=> 
                            (not 
                                __tmp_4
                            ) 
                            (and 
                                (and 
                                    (= 
                                        NSMain__max___ir_ret_ 
                                        NSMain__max__y
                                    ) 
                                    MIRJumpFormula
                                ) 
                                (and 
                                    (and 
                                        (and 
                                            (=> 
                                                __tmp_0 
                                                (= 
                                                    NSMain__max___ir_ret_$3 
                                                    NSMain__max___ir_ret_$2
                                                )
                                            ) 
                                            (=> 
                                                __tmp_4 
                                                (= 
                                                    NSMain__max___ir_ret_$3 
                                                    NSMain__max___ir_ret_$1
                                                )
                                            )
                                        ) 
                                        (=> 
                                            (not 
                                                __tmp_4
                                            ) 
                                            (= 
                                                NSMain__max___ir_ret_$3 
                                                NSMain__max___ir_ret_
                                            )
                                        )
                                    ) 
                                    (= 
                                        NSMain__max___ir_ret_$3 
                                        NSMain__max___return_
                                    )                                
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)