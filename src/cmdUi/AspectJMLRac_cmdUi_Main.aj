import cmdUi.*;
import org.jmlspecs.ajmlrac.runtime.*;
import org.jmlspecs.lang.annotation.*;
import java.util.Map;


privileged aspect AspectJMLRac_cmdUi_Main10bfefcc_584f_4add_b7f5_c2efff964b42 {

 declare precedence: AspectJMLRac_*, *;


  /** Generated by AspectJML to check the exceptional postcondition of
   * method main. */
   after (final java.lang.String[] args) throwing (Throwable rac$e) :
     execution(static void cmdUi.Main.main(java.lang.String[])) && args(args) {
           JMLChecker.rethrowJMLAssertionError(rac$e, "cmdUi.Main.main(java.lang.String[])");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.Main.java\" by method cmdUi.Main.main\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.Main.main regarding code at \nFile \"cmdUi.Main.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, "cmdUi.Main.main(java.lang.String[])", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method print. */
   after (final java.lang.Object e) throwing (Throwable rac$e) :
     execution(static void cmdUi.Main.print(java.lang.Object)) && args(e) {
           JMLChecker.rethrowJMLAssertionError(rac$e, "cmdUi.Main.print(java.lang.Object)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.Main.java\" by method cmdUi.Main.print\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.Main.print regarding code at \nFile \"cmdUi.Main.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, "cmdUi.Main.print(java.lang.Object)", rac$e);
  		 }
  		   }
  	 }



  /** Generated by AspectJML to check the precondition of
   * method main. */
  before (final java.lang.String[] args) :
     execution(static void cmdUi.Main.main(java.lang.String[])) && args(args) {
       String preErrorMsg = "by method cmdUi.Main.main regarding code at \nFile \"cmdUi.Main.java\""+", when \n"+"\t\'args\' is "+args+ ", when \n"+"\t\'args\' is "+args;
       String evalErrorMsg = "Invalid expression in \"cmdUi.Main.java\"\nCaused by: ";
       boolean rac$b = true;
       try {
        rac$b = (args != null);
       } catch (JMLNonExecutableException rac$nonExec) {
          rac$b = false;
       } catch (Throwable rac$cause) {
          if(rac$cause instanceof JMLAssertionError) {
            throw (JMLAssertionError) rac$cause;
          }
          else {
            throw new JMLEvaluationError(evalErrorMsg + rac$cause);
          }
       }
       boolean canThrow = true;
       JMLChecker.checkPrecondition(rac$b, canThrow, preErrorMsg, -1, "cmdUi.Main.main(java.lang.String[])");

     }

  /** Generated by AspectJML to check the precondition of
   * method print. */
  before (final java.lang.Object e) :
     execution(static void cmdUi.Main.print(java.lang.Object)) && args(e) {
       String preErrorMsg = "by method cmdUi.Main.print regarding code at \nFile \"cmdUi.Main.java\""+", when \n"+"\t\'e\' is "+e+ ", when \n"+"\t\'e\' is "+e;
       String evalErrorMsg = "Invalid expression in \"cmdUi.Main.java\"\nCaused by: ";
       boolean rac$b = true;
       try {
        rac$b = (e != null);
       } catch (JMLNonExecutableException rac$nonExec) {
          rac$b = false;
       } catch (Throwable rac$cause) {
          if(rac$cause instanceof JMLAssertionError) {
            throw (JMLAssertionError) rac$cause;
          }
          else {
            throw new JMLEvaluationError(evalErrorMsg + rac$cause);
          }
       }
       boolean canThrow = true;
       JMLChecker.checkPrecondition(rac$b, canThrow, preErrorMsg, -1, "cmdUi.Main.print(java.lang.Object)");

     }



  /** Generated by AspectJML to enable modular signals_only checking (XCS enabled) */
    after(final cmdUi.Main object$rac): (execution( * cmdUi.Main..*+.*(..))
            || execution(cmdUi.Main..*+.new(..))
            || execution( * cmdUi.Main+.*(..))
            || execution(cmdUi.Main+.new(..))) && 
     this(object$rac) {
     JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();
    }

  /** Generated by AspectJML to enhance error reporting (Execution Site enabled) */
    after() throwing (Throwable rac$e): (execution( * cmdUi.Main..*+.*(..))
            || execution(cmdUi.Main..*+.new(..))
            || execution( * cmdUi.Main+.*(..))
            || execution(cmdUi.Main+.new(..))){
      JMLChecker.hideAjmlSpecificStackTrace(rac$e);
    }
}
