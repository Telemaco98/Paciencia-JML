package cmdUi.menu;

import cmdUi.Main;
import controller.Controller;

public class ConfigMenu extends AbstractMenu{
	
	/*@ requires   parent != null || con != null;
	  @ assignable this.con;
	  @ assignable this.options;
	  @ assignable this.parent;
	  @ ensures    this.con == con;
	  @ ensures    this.options == options;
	  @ ensures    this.parent == parent;
	  @*/
	public ConfigMenu(Controller con, int options, AbstractMenu parent) {
		super(con, options, parent);
	}

	@Override
	public /*@ pure @*/ void draw() {
		Main.print("\n");
		Main.print("1 - PUXAR UMA CARTA DO ESTOQUE\n");
		Main.print("2 - PUXAR TRES CARTAS DO ESTOQUE\n");
	}

	@Override
	public /*@ pure @*/ AbstractMenu processInput(int op) {
		switch (op) {
		case 1: con.setPuxarUmaCartaEstoque(); break;
		case 2: con.setPuxarTresCartasEstoque(); break;
		}
		return parent;
	}
}
