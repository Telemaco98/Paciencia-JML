package cmdUi.menu;

import java.util.Scanner;

import cmdUi.Main;
import controller.Controller;

public abstract class AbstractMenu {
	protected /*@ spec_public nullable @*/ Controller con;
	protected /*@ spec_public nullable @*/ AbstractMenu parent;
	protected /*@ spec_public @*/ int options;
	protected /*@ spec_public @*/ Scanner sc;
	
	/*@ requires   parent != null || con != null;
	  @ assignable this.con;
	  @ assignable this.options;
	  @ assignable this.parent;
	  @ assignable this.sc;
	  @ ensures    this.con == con;
	  @ ensures    this.options == options;
	  @ ensures    this.parent == parent;
	  @*/
	protected AbstractMenu(Controller con, int options, AbstractMenu parent) {
		this.con = con;
		this.parent = parent;
		this.options = options;
		sc = new Scanner(System.in);
	}
	
	public abstract /*@ pure @*/ void draw();
		
	public abstract /*@ pure @*/ AbstractMenu processInput(int op);
	
	public /*@ pure @*/boolean isOptionValid(int option) {
		return (option >= 1 && option <= options);
	}
	
	/**Receber uma escolha de opção do usuário
	 * @return Opção entrada*/
	public /*@ pure @*/ int getOptionInput() {
		int op = sc.nextInt();
		
		while (!isOptionValid(op)) {
			Main.print("\nInsira uma opção válida.\n");
			op = sc.nextInt();
		}
		
		return op;		
	}
}
