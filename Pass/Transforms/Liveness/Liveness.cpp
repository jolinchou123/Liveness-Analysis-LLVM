#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Value.h"
#include <string>
#include <map>
#include <typeinfo>
#include "llvm/IR/CFG.h"
#include <list>
#include <iterator>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "Liveness"

using namespace llvm;

namespace {
struct Liveness : public FunctionPass {
    string func_name = "test";
    static char ID;
    Liveness() : FunctionPass(ID) {}
    
    bool runOnFunction(Function &F) override {
        errs() << "Liveness Analysis: " << F.getName() << "\n";
        
        // Initialize variable sets for Liveness Analysis
        vector<string> varKill = {};
        vector<string> ueVar = {};

        string temp1, temp2;

        bool con = true;
        int count_suc = 0;
        
        vector<string> varKill_suc = {};
        vector<string> ueVar_suc = {};
        vector<string> live_temp1 = {}, live_temp2 = {}, live_temp3 = {};
        vector<string> dest1 = {}, dest2 = {}, dest11 = {}, dest22 = {}, dest3 = {};
        vector<string> live_new = {};
        vector<string> print_liveout = {};
        
        // Liveout Set map
        map<string, vector<string>> liveOut;
        
        //start iteration and deal with back edges
        while(con){
            con = false;
            for(auto& basic_block : F){
                //compute the number of the successors for block N
                for(BasicBlock *Succ : successors(&basic_block)){
                    count_suc++;
                }

                //compute LIVEOUT(N) for each block X, X belongs to SUCC(N)
                int j = 0;
                for(BasicBlock *Succ : successors(&basic_block)){
                    //errs() << Succ->getName() << "\n";
                    for(auto& inst : *Succ){
                        //compute VARKILL(X) for each block X
                        if(inst.getOpcode() == Instruction::Store){
                            //errs() << inst.getOperand(0)->getName().str() << "\n";
                            if(find(varKill_suc.begin(), varKill_suc.end(), inst.getOperand(1)->getName().str()) == varKill_suc.end()){
                                auto it = varKill_suc.insert(varKill_suc.end(), inst.getOperand(1)->getName().str());
                            }
                        }
                        //compute UEVAR(X) for each block X
                        if((inst.getOpcode()==Instruction::Store) && (inst.getOperand(0)->getName().str() == "")){
                            User* abcde = dyn_cast<User>(inst.getOperand(0));
                            if((find(varKill_suc.begin(), varKill_suc.end(), abcde->getOperand(0)->getName().str())==varKill_suc.end()) && (find(ueVar_suc.begin(), ueVar_suc.end(), abcde->getOperand(0)->getName().str())==ueVar_suc.end())){
                                auto it = ueVar_suc.insert(ueVar_suc.end(), abcde->getOperand(0)->getName().str());
                            }
                        }
                        if((inst.isBinaryOp()) || (inst.getOpcode()==Instruction::ICmp)){
                            auto* ptr = dyn_cast<User>(&inst);
                            int i = 0;
                            for(auto it=ptr->op_begin(); it!=ptr->op_end(); ++it){
                                User* instr = dyn_cast<User>(it);
                                if(i == 0){
                                    temp1 = instr->getOperand(0)->getName().str();
                                    if((temp1!="") && (find(varKill_suc.begin(), varKill_suc.end(), temp1)==varKill_suc.end()) && (find(ueVar_suc.begin(), ueVar_suc.end(), temp1)==ueVar_suc.end())){
                                        auto it = ueVar_suc.insert(ueVar_suc.end(), temp1);
                                    }
                                }else{
                                    temp2 = instr->getOperand(0)->getName().str();
                                    if((temp2!="") && (find(varKill_suc.begin(), varKill_suc.end(), temp2)==varKill_suc.end()) && (find(ueVar_suc.begin(), ueVar_suc.end(), temp2)==ueVar_suc.end())){
                                        auto it = ueVar_suc.insert(ueVar_suc.end(), temp2);
                                    }
                                }
                                i++;
                            }
                        }
                    }
                    if(count_suc == 2){
                        if(j == 0){
                            auto search = liveOut.find(Succ->getName().str());
                            if(search == liveOut.end()){
                                live_temp1 = {};
                                set_difference(live_temp1.begin(), live_temp1.end(), varKill_suc.begin(), varKill_suc.end(),back_inserter(dest1));
                                set_union(dest1.begin(), dest1.end(), ueVar_suc.begin(), ueVar_suc.end(),std::back_inserter(dest11));
                            }else{
                                live_temp1 = search->second;
                                set_difference(live_temp1.begin(), live_temp1.end(), varKill_suc.begin(), varKill_suc.end(),back_inserter(dest1));
                                set_union(dest1.begin(), dest1.end(), ueVar_suc.begin(), ueVar_suc.end(),std::back_inserter(dest11));
                            }
                            j++;
                        }else{
                            auto search = liveOut.find(Succ->getName().str());
                            if(search == liveOut.end()){
                                live_temp2 = {};
                                set_difference(live_temp2.begin(), live_temp2.end(), varKill_suc.begin(), varKill_suc.end(),back_inserter(dest2));
                                set_union(dest2.begin(), dest2.end(), ueVar_suc.begin(), ueVar_suc.end(),std::back_inserter(dest22));
                            }else{
                                live_temp2 = search->second;
                                set_difference(live_temp2.begin(), live_temp2.end(), varKill_suc.begin(), varKill_suc.end(),back_inserter(dest2));
                                set_union(dest2.begin(), dest2.end(), ueVar_suc.begin(), ueVar_suc.end(),std::back_inserter(dest22));
                            }
                        }
                        set_union(dest11.begin(), dest11.end(), dest22.begin(), dest22.end(),std::back_inserter(live_new));
                    }else if(count_suc == 1){
                        auto search = liveOut.find(Succ->getName().str());
                        if(search == liveOut.end()){
                            live_temp3 = {};
                            set_difference(live_temp3.begin(), live_temp3.end(), varKill_suc.begin(), varKill_suc.end(),back_inserter(dest3));
                            set_union(dest3.begin(), dest3.end(), ueVar_suc.begin(), ueVar_suc.end(),std::back_inserter(live_new));
                        }else{
                            live_temp3 = search->second;
                            set_difference(live_temp3.begin(), live_temp3.end(), varKill_suc.begin(), varKill_suc.end(),back_inserter(dest3));
                            set_union(dest3.begin(), dest3.end(), ueVar_suc.begin(), ueVar_suc.end(),std::back_inserter(live_new));
                        }
                    }
                    ueVar_suc.clear();
                    varKill_suc.clear();
                    dest1.clear();
                    dest2.clear();
                    dest3.clear();
                    live_temp1.clear();
                    live_temp2.clear();
                    live_temp3.clear();
                    
                }
                dest11.clear();
                dest22.clear();

                auto search = liveOut.find(basic_block.getName().str());

                //remove duplicate values in vectors
                sort(live_new.begin(), live_new.end());
                live_new.erase(unique(live_new.begin(), live_new.end()), live_new.end());

                if(search == liveOut.end()){
                    con = true;
                    liveOut.insert(pair<string, vector<string>>(basic_block.getName().str(), live_new));
                }else{
                    if(search->second != live_new){
                        search->second = live_new;
                        con = true;
                    }
                }

                //clean for next block
                live_new.clear();
                count_suc = 0;
            }
        } // end while
        
        for(auto& basic_block : F){
            for(auto& inst : basic_block){
                //compute VARKILL(N) for each block N
                if(inst.getOpcode() == Instruction::Store){
                    if(find(varKill.begin(), varKill.end(), inst.getOperand(1)->getName().str()) == varKill.end()){
                        auto it = varKill.insert(varKill.end(), inst.getOperand(1)->getName().str());
                    }
                }
                //compute UEVAR(N) for each block N
                if((inst.getOpcode()==Instruction::Store) && (inst.getOperand(0)->getName().str() == "")){
                    User* abcde = dyn_cast<User>(inst.getOperand(0));
                    if((find(varKill.begin(), varKill.end(), abcde->getOperand(0)->getName().str())==varKill.end()) && (find(ueVar.begin(), ueVar.end(), abcde->getOperand(0)->getName().str())==ueVar.end())){
                         auto it = ueVar.insert(ueVar.end(), abcde->getOperand(0)->getName().str());
                    }
                }
                if((inst.isBinaryOp()) || (inst.getOpcode()==Instruction::ICmp)){
                    auto* ptr = dyn_cast<User>(&inst);
                    int i = 0;
                    for(auto it=ptr->op_begin(); it!=ptr->op_end(); ++it){
                        User* instr = dyn_cast<User>(it);
                        if(i == 0){
                            temp1 = instr->getOperand(0)->getName().str();
                            if((temp1!="") && (find(varKill.begin(), varKill.end(), temp1)==varKill.end()) && (find(ueVar.begin(), ueVar.end(), temp1)==ueVar.end())){
                                auto it = ueVar.insert(ueVar.end(), temp1);
                            }
                        }else{
                            temp2 = instr->getOperand(0)->getName().str();
                            if((temp2!="") && (find(varKill.begin(), varKill.end(), temp2)==varKill.end()) && (find(ueVar.begin(), ueVar.end(), temp2)==ueVar.end())){
                                auto it = ueVar.insert(ueVar.end(), temp2);
                            }
                        }
                        i++;
                    }
                }
            }
            errs() << "-----" << basic_block.getName() << "-----\n";
            errs() << "UEVAR: ";
            sort(ueVar.begin(), ueVar.end());
            for (auto it=ueVar.begin(); it!=ueVar.end(); ++it){
                errs() << *it << " ";
            }
            errs() << "\n" << "VARKILL: ";
            sort(varKill.begin(), varKill.end());
            for (auto it=varKill.begin(); it!=varKill.end(); ++it){
                errs() << *it << " ";
            }
            errs() << "\n" << "LIVEOUT: ";
            auto search_again = liveOut.find(basic_block.getName().str());
            print_liveout = search_again->second;
            for (auto it=print_liveout.begin(); it!=print_liveout.end(); ++it){
                errs() << *it << " ";
            }
            errs() << "\n";

            //clean for next block
            ueVar.clear();
            varKill.clear();
            print_liveout.clear();
        } // end basic blocks

    } // end runOnFunction
}; // end of struct Liveness
} // end of enonymous namespace
char Liveness::ID = 0;
static RegisterPass<Liveness> X("Liveness", "Liveness Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
