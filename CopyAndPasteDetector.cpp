//===-  islClan.cpp ---------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Example clang plugin which simply prints the names of all the top-level decls
// in the input file.
//
//===----------------------------------------------------------------------===//

// clang llvm
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "llvm/Support/raw_ostream.h"

// std
#include <fstream>
#include <chrono>
#include <iostream>
#include <map>
#include <string>
#include <memory>
#include <mutex>

// logging 
#include "plog/Log.h"
#include "plog/Appenders/ConsoleAppender.h"


using namespace clang;
using namespace clang::ast_matchers;

namespace {

std::map<const Expr*, std::vector<const Expr*>> similar_expressions;
std::vector<std::set<const Expr*>> similar_sets;

std::set<const Expr*>* find_set( const Expr* element ) {
  for( auto& similar_set : similar_sets ){
    if ( similar_set.find(element) != similar_set.end() ){
      return &similar_set;
    }
  }
  
  return nullptr;
}

class ExpressionVisitor : public clang::RecursiveASTVisitor<ExpressionVisitor> {
public:

  ExpressionVisitor( const Expr* _target ) :
    target(_target)
  {

  }

  bool VisitExpr( const Expr* expr ) {

    // don't count yourself as a duplicate
    if ( expr == target ) {
      return true;
    }

    // same statement class 
    if ( expr->getStmtClass() == target->getStmtClass() ){

      int n_children_expr = std::distance( expr->child_begin(), expr->child_end() );
      if ( n_children_expr == 0 ) {
        LOGD << "found another node that is similar to the target";
        expr->dump();      
        similar_expressions[target].push_back(expr);
      }else{

        // number of children has to be the same
        int n_children_target = std::distance( target->child_begin(), target->child_end() );
        if ( n_children_target == n_children_expr ) {
          LOGD << "number of children is the same";

          bool all_children_similar = true;
          // iterate over both
          for ( 
            auto tchild = target->child_begin(), 
            echild = expr->child_begin() ;
            tchild != target->child_end() && echild != expr->child_end() ;
            echild++, tchild++ ){

            // all children need to be similar
            if ( auto set = find_set( (Expr*)*tchild ) ) {
              LOGD << "found the set for the target";
              if ( set->find( (Expr*) *echild ) != set->end() ) {
                LOGD << "found that expr child is in the same set as targets child";
              }else{
                all_children_similar = false;
                break;
              }
            }else{
              all_children_similar = false;
              break;
            }
          }

          if ( all_children_similar ) {
            similar_expressions[target].push_back( expr );
          }

        }
        
      }


    }

    return true;
  }

private:
  const Expr* target;

};


class Callback : public MatchFinder::MatchCallback {
  public:
    Callback ( ASTContext& _clang_ctx ) :
      clang_ctx(_clang_ctx) 
    {

    }
    // is the function that is called if the matcher finds something
    virtual void run(const MatchFinder::MatchResult& Result) {
      ASTContext& context = *Result.Context;
      SourceManager& SM = context.getSourceManager();
      auto& diags = context.getDiagnostics();

      if (auto expr = Result.Nodes.getNodeAs<Expr>("expr")) {

        // check that they are not already in the similar_sets
        for( auto&& similar_set : similar_sets ){
          if ( similar_set.find( expr ) != similar_set.end() ) {
            return;
          } 
        }

        expr->dump();
        // TODO visitor to find other expressions that have the same type but not the same 
        // pointer identity
        ExpressionVisitor expression_visitor(expr);
        auto tu = context.getTranslationUnitDecl();
        expression_visitor.TraverseDecl( tu );
        LOGD << "\n";
      }


    }
  private:
    ASTContext& clang_ctx;

};



class ForLoopConsumer : public ASTConsumer {
public:
  
  ForLoopConsumer(  ) 
  { 
    LOGD << "for loop consumer created " << this ;
  }

  ~ForLoopConsumer(){
    LOGD << "for loop consumer destroyed " << this ;
  }


  // match all leaf nodes
  StatementMatcher makeLeafMatcher(){
    return expr(
        unless(
          hasDescendant(
            expr()
          )
        )
    ).bind("expr");
  }

  // match all expressions
  StatementMatcher makeExprMatcher(){
    return expr( ).bind("expr");
  }

  void compress_results() {
    for( auto&& key_value_pair : similar_expressions ){
      bool found = false;
      for( auto&& similar_set : similar_sets ){
        auto res = similar_set.find(key_value_pair.first);
        if ( res != similar_set.end() ) {
          found = true;
        }
      }

      if ( !found ) {
        std::set<const Expr*> set;
        set.insert( key_value_pair.first );
        for( auto& other : key_value_pair.second ){
            set.insert( other );
        }
        similar_sets.push_back( set );
      }
    }
     
    LOGD << "there are " << similar_sets.size() << "sets" ;
    int ctr = 0;
    for( auto&& similar_set : similar_sets ){
      LOGD << "set " << ctr++; 
      for( auto&& element : similar_set ){
          LOGD << element;
      }
      
    }

    similar_expressions.clear();
    
  }

  void print_similar_expressions(){
    LOGD << "similar expressions are";

    for( auto&& element : similar_expressions ){
      element.first->dumpColor();
      LOGD << "is similar to";
      for( auto&& element : element.second ){
          element->dumpColor();
      }
      LOGD << "\n"; 
    }
  }

  void HandleTranslationUnit( ASTContext& clang_ctx ) {

    auto begin = std::chrono::high_resolution_clock::now();

    // first step search leaf nodes
    {
      MatchFinder Finder;
      Callback Fixer(clang_ctx);
      Finder.addMatcher( makeLeafMatcher(), &Fixer);
      Finder.matchAST(clang_ctx);
    }

    print_similar_expressions();

    // now do this for some steps
    while ( true ) {
      if ( similar_expressions.size() == 0 ) {
        break;
      }
      compress_results();

      MatchFinder Finder;
      Callback Fixer(clang_ctx);
      Finder.addMatcher( makeExprMatcher(), &Fixer);
      Finder.matchAST(clang_ctx);
      print_similar_expressions();
    }

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end-begin;
    LOGD << "plugin: time consumption " << diff.count() << " s" ;
  }

private: 

};

class CopyAndPasteDetectorAction : public PluginASTAction {

  public:
    CopyAndPasteDetectorAction(){
      static bool once = true;
      if ( once ) {
	static plog::ConsoleAppender<plog::TxtFormatter> consoleAppender;
	plog::init(plog::debug, &consoleAppender); 
	once = false;
	LOGD << "logger initialized ";
      }

      LOGD << "clang action " << this << " created " ;
    }

    virtual ~CopyAndPasteDetectorAction(){
      LOGD << "clang action " << this << " destroyed ";
    }

    // Automatically run the plugin after the main AST action
    PluginASTAction::ActionType getActionType() override {
      return AddAfterMainAction;
    }

protected:

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, llvm::StringRef) override;
  bool ParseArgs(const CompilerInstance &CI, const std::vector<std::string> &args) override;
  void PrintHelp(llvm::raw_ostream& ros) {
    ros << "run the plugin with -emit-[openmp,openacc,hpx,tbb,cilk] to get different implementations for the loops\n";
  }


};


std::unique_ptr<ASTConsumer> 
CopyAndPasteDetectorAction::CreateASTConsumer(CompilerInstance &CI, llvm::StringRef){

  auto& diags = CI.getDiagnostics();
  if ( diags.hasErrorOccurred() ) {
    LOGD << "an error has occurred before the compiler";
  }else{
    LOGD << "no error occurred adding plugin";
  }

  LOGD << "makeing new Consumer object with compiler instance " << &CI ;
  auto ret =  llvm::make_unique<ForLoopConsumer>();
  LOGD << "at load ci " << ret.get() << " instance " << &CI << " ast context " << &CI.getASTContext() << " SM " << &CI.getSourceManager() ;
  LOGD << "done with the new consumer object" ;

  // TODO find all header includs in the main file and pass them to the ForLoopConsumer

  return std::move(ret);
}

bool 
CopyAndPasteDetectorAction::ParseArgs(const CompilerInstance &CI, const std::vector<std::string> &args)  {
  std::string* next_arg = nullptr;

  for (unsigned i = 0, e = args.size(); i != e; ++i) {
    LOGD << "Clan arg = " << args[i];

    if ( next_arg ) {
      *next_arg = args[i];
      next_arg = nullptr;
      continue;
    }
  }

  return true;
}


} // namespace end

// TODO change name
static FrontendPluginRegistry::Add<CopyAndPasteDetectorAction>
X("cpd", "run dd as part of the compiler");
