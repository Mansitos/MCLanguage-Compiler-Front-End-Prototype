module TacGen where

import AbsTac as Tac
import AbsProgettoPar as Abs
import TypeChecker
import Type

-- Given the start of a program (starting node Abs.S); starts the TAC generation process
genTAC :: Abs.S TCheckResult -> Abs.S TAC
genTAC (Abs.StartCode tres stats) = let endLab = Label ("end",0) in
                                        let statsTac = (genTacStatements stats) in
                                            let tacs = (statements_content statsTac) in
                                                (Abs.StartCode (TAC ((tacs):(TacLabel endLab):(ExitTac))) statsTac)

genTacStatements :: Abs.STATEMENTS TCheckResult -> Abs.STATEMENTS TAC
genTacStatements (Abs.ListStatements tres stat stats) = (Abs.ListStatements (TAC []) (genTacStatement stat) (genTacStatements stats)) 
genTacStatements (Abs.EmptyStatement tres)            = (Abs.EmptyStatement (TAC []) ) 

genTacStatement :: Abs.STATEMENT TCheckResult -> Abs.STATEMENT TAC
{-genTacStatement Abs.BreakStatement tres)                           = 
genTacStatement (Abs.ContinueStatement tres)                        = 
genTacStatement (Abs.ReturnStatement tres ret)                      = 
genTacStatement (Abs.Statement tres block)                          =
genTacStatement (Abs.ExpressionStatement tres exp)                  =
genTacStatement (Abs.AssignmentStatement tres lval assignOp exp)    =
genTacStatement (Abs.VariableDeclarationStatement tres tipo vardec) = (Abs.VariableDeclarationStatement (TAC []) (genTacVariableDeclarationStatement vardec))-}
genTacStatement (Abs.ConditionalStatement tres condition)           = (Abs.ContinueStatement (TAC [])){-
genTacStatement (Abs.WhileDoStatement tres whileStaement)           = 
genTacStatement (Abs.DoWhileStatement tres doStatement)             = 
genTacStatement (Abs.ForStatement tres forStatement)                = 
genTacStatement (Abs.ProcedureStatement tres id param states)       =                                              
genTacStatement (Abs.FunctionStatement tres id param tipo states)   =-}
