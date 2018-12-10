package cmdUi;

import cmdUi.menu.AbstractMenu;
import cmdUi.menu.MainMenu;
import controller.Controller;
import util.View;

/**Cuida do controle entre qual tela de menu deve ser mostrada a cada momento.*/
public class CmdView implements View{

	/**Controller do jogo Paciência*/
	private /*@ spec_public nullable @*/ Controller con;
	
	/**Tela atual com menu*/
	private /*@ spec_public @*/ AbstractMenu currentMenu;
	
	/*@ ensures con != null;
	  @ ensures currentMenu != null;
	  @*/
	public CmdView() {
		con = new Controller(this);
		currentMenu = new MainMenu(con,5);
	}
	
	/**Inicia o loop onde a tela é desenhada, o sistema espera uma entrada, e logo depois, realiza uma ação.*/
	public /*@ pure @*/ void start() {
		
		while (true) {
			currentMenu.draw();
			int op = currentMenu.getOptionInput();
			currentMenu = currentMenu.processInput(op);
		}
	}

	@Override
	public /*@ pure @*/ void drawOnScreen() {}
}
