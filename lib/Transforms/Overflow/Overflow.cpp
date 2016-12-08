//===- Overflow.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Overflow" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Constants.h>
#include "llvm/Support/raw_ostream.h"
#include <llvm/IR/PatternMatch.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Utils/Local.h>
using namespace llvm;
using namespace llvm::PatternMatch;

/*
Reference: 
http://llvm.org/docs/WritingAnLLVMPass.html#quick-start-writing-hello-world
http://llvm.org/docs/doxygen/html/SimplifyCFGPass_8cpp_source.html
http://llvm.org/docs/doxygen/html/Local_8cpp_source.html
https://gist.github.com/xiw/3429064
*/

#define DEBUG_TYPE "overflow"

namespace {
    struct Overflow : public FunctionPass 
    {
        static char ID; // Pass identification, replacement for typeid
        Overflow() : FunctionPass(ID) 
        {
            mBuilder = nullptr;
        }

        virtual void getAnalysisUsage(AnalysisUsage& info) const 
        {
            info.setPreservesCFG();
        }

        virtual bool runOnFunction(Function &F) 
        {
            IRBuilder<> cur_bdr(F.getContext());
            mBuilder = &cur_bdr;
            bool changed = false;
            inst_iterator start = inst_begin(F);
            while(start != inst_end(F))
            {
                ICmpInst *I = dyn_cast<ICmpInst>(&*start);
                ++start;
                if (!I)
                  continue;
                Value *L = I->getOperand(0), *R = I->getOperand(1);
                if (!L->getType()->isIntegerTy())
                  continue;
                mBuilder->SetInsertPoint(I);
                Value *V = matchCmpWithSwappedAndInverse(I->getPredicate(), L, R);
                if (V)
                {
                    I->replaceAllUsesWith(V);
                    if (I->hasName()) V->takeName(I);
                    RecursivelyDeleteTriviallyDeadInstructions(I);
                    changed = true;
                }
            }
            return changed;
        }

        private:
        IRBuilder<>* mBuilder;

        Value* matchCmp(CmpInst::Predicate Pred, Value *L, Value *R) 
        {
            Value *X, *Y, *A, *B;
            Value *Zero = 0;
            //ConstantInt *C;
            switch(Pred)
            {
                // x >0 && y > 0 && x + y < x || x + y < y => add overflow
                // x >0 && y < 0 && x - y < x => add overflow
                // x <0 && y > 0 && y - x < y || => add overflow
                case CmpInst::ICMP_SLT:
                    if(
                    (X > Zero && Y > Zero
                    &&match(L, m_Add(m_Value(X), m_Value(Y)))
                    && match(R, m_Value(A))
                    && (A == X || A == Y))
                    ||
                    (X > Zero && Y < Zero
                    &&match(L, m_Sub(m_Value(X), m_Value(Y)))
                    && match(R, m_Value(A))
                    && (A == X))
                    ||
                    (X < Zero && Y > Zero
                    &&match(L, m_Sub(m_Value(Y), m_Value(X)))
                    && match(R, m_Value(A))
                    && (A == Y))
                    )
                    return createOverflowBit(Intrinsic::sadd_with_overflow, X, Y);
                    break;

                // x >0, y>0, x != (x * y) / y || x != (y * x) / y => mul overflow
                case CmpInst::ICMP_NE:
                    if(match(L, m_Value(X))
                    && match(R, m_SDiv(m_Mul(m_Value(A), m_Value(B)), m_Value(Y)))
                    && ((A == X && B == Y) || (A == Y && B == X)))
                    return createOverflowBit(Intrinsic::smul_with_overflow, X, Y);
                    break;

                // x < 0, y < 0, x - y > x || x - y  > y => add overflow
                // x > max - y => add overflow
                case CmpInst::ICMP_SGT:
                    if(
                    X < Zero && Y < Zero
                    &&match(L, m_Add(m_Value(X), m_Value(Y)))
                    && match(R, m_Value(A))
                    && (A == X || A == Y)
                    )
                    return createOverflowBit(Intrinsic::sadd_with_overflow, X, Y);

                    if(
                    X > Zero && Y > Zero
                    &&match(L, m_Value(X))
                    && match(R, m_Sub(m_AllOnes(), m_Value(Y)))
                    )
                    return createOverflowBit(Intrinsic::sadd_with_overflow, X, Y);
                    break;
                default:
                    return nullptr;
            }
            return nullptr;
        }

        Value *createOverflowBit(Intrinsic::ID ID, Value *L, Value *R) {
            Module *M = mBuilder->GetInsertBlock()->getParent()->getParent();
            Function *F = Intrinsic::getDeclaration(M, ID, L->getType());
            CallInst *CI = mBuilder->CreateCall(F, {L, R});
            return mBuilder->CreateExtractValue(CI, 1);
        }

        Value *matchCmpWithSwappedAndInverse(CmpInst::Predicate Pred, Value *L, Value *R)         {
            if (Value *V = matchCmpWithInverse(Pred, L, R))
              return V;
            Pred = CmpInst::getSwappedPredicate(Pred);
            if (Value *V = matchCmpWithInverse(Pred, R, L))
              return V;
            return NULL;
        }

        Value *matchCmpWithInverse(CmpInst::Predicate Pred, Value *L, Value *R) {
            if (Value *V = matchCmp(Pred, L, R))
              return V;
            Pred = CmpInst::getInversePredicate(Pred);
            if (Value *V = matchCmp(Pred, L, R))
              return mBuilder->CreateXor(V, 1);
            return NULL;
        }
    };
}

char Overflow::ID = 0;
static RegisterPass<Overflow> X("overflow", "Overflow Pass");
