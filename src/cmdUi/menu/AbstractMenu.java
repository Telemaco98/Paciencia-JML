package cmdUi.menu;

import java.util.Scanner;

import cmdUi.Main;
import controller.Controller;

public abstract class AbstractMenu {
	protected /*@ spec_public nullable @*/ Controller con;
	protected  /*@ spec_public nullable @*/ AbstractMenu parent;
	protected int options;
	protected Scanner sc;
	
	/*@ requires parent != null;
	  @*/
	protected AbstractMenu(Controller con, int options, AbstractMenu parent) {
		this.con = con;
		this.parent = parent;
		this.options = options;
		sc = new Scanner(System.in);
	}
	
	public abstract void draw();
		
	public abstract AbstractMenu processInput(int op);
	
	public boolean isOptionValid(int option) {
		return (option >= 1 && option <= options);
	}
	
	/**Receber uma escolha de opção do usuário
	 * @return Opção entrada*/
	public int getOptionInput() {
		int op = sc.nextInt();
		
		while (!isOptionValid(op)) {
			Main.print("\nInsira uma opção válida.\n");
			op = sc.nextInt();
		}
		
		return op;		
	}
}
