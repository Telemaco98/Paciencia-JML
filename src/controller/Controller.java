package controller;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;

import cmdUi.CmdView;

import config.Configuracao;
import model.Mesa;
import model.Mesa.GameStatus;
import model.Pilha;
import util.Baralho;
import util.Observer;
import util.View;


public class Controller implements Observer{

	private /*@ spec_public nullable @*/ Mesa mesa;
	private /*@ spec_public nullable @*/ View view;
	private /*@ spec_public nullable @*/ Instant start;
	private /*@ spec_public nullable @*/ Instant end;
	
	/*@ requires view != null;
	  @ assignable this.view;
	  @ ensures    this.view == view;
	  @*/
	public Controller(View view) {
		this.view = view;
		iniciarJogo();
	}
	
	/*@ assignable this.mesa, this.start;
	  @ ensures    this.mesa != null;
	  @ ensures	   this.mesa.getObservers().contains(this);
	  @*/
	public void iniciarJogo() {
		start = Instant.now();
		mesa = new Mesa(new Baralho(true));
		mesa.addObserver(this);
	}
	
	/**Wrapper function para o moverCartas da mesa*/
	
	/*@ requires   1 <= valorReferencia && valorReferencia <= 13;
	  @ requires   1 <= origem && origem <= 13;
	  @ requires   1 <= destino && destino <= 13;
	  @ assignable this.mesa;
	  @*/
	public boolean moverCartas(int origem, int destino, int valorReferencia) {
		return mesa.moverCartas(origem, destino, valorReferencia);
	}
	
	/**Wrapper function para o moverCartaTopo da mesa*/
	/*@ requires   1 <= origem && origem <= 13;
	  @ requires   1 <= destino && destino <= 13;
	  @ assignable this.mesa;
	  @*/
	public boolean moverCartaTopo(int origem, int destino) {
		return mesa.moverCartaTopo(origem, destino);
	}
	
	/**Checa se o jogador já venceu e, caso afirmativo, guarda o momento de fim do jogo.*/
	public /*@ pure @*/ boolean isVencedor() {
		boolean res = mesa.getGameStatus()==GameStatus.VENCIDO;
		if (res) {
			end = Instant.now();
		}
		return res;
	}
	
	/**Wrapper function para o virarCartaFileira da mesa*/
	/*@ assignable this.mesa;
	  @*/
	public void virarCartaFileira(int index) {
		mesa.virarCartaFileira(index);
	}
	
	/**Wrapper function para o puxarCartaEstoque da mesa*/
	/*@ assignable this.mesa;
	  @*/
	public void puxarCartaEstoque() {
		mesa.puxarCartasEstoque();
	}
	
	/**Muda as configurações do jogo para puxar 3 cartas do estoque*/
	/*@ ensures    Configuracao.getInstance().getQtdCartasPuxadasEstoque() == 3;
	  @*/
	public void setPuxarTresCartasEstoque() {
		Configuracao.getInstance().setModoEstoque(Configuracao.PUXAR_TRES_CARTAS);
	}
	
	/**Muda as configurações do jogo para puxar 1 carta do estoque*/
	/*@ ensures    Configuracao.getInstance().getQtdCartasPuxadasEstoque() == 1;
	  @*/
	public void setPuxarUmaCartaEstoque() {
		Configuracao.getInstance().setModoEstoque(Configuracao.PUXAR_UMA_CARTA);
	}
	
	/**Finaliza o jogo*/
	public /*@ pure @*/ void finalizar(){
		System.exit(0);
	}
	
	/**Pega as pilhas para poderem ser visualizadas em uma interface
	 * @return Pilhas da mesa*/
	public /*@ pure @*/ ArrayList<Pilha> getPilhas() {
		return mesa.getPilhas();
	}
	
	
	/**Duração total do jogo.
	 * @return Duração do jogo*/
	/*@ requires this.start != null;
	  @ requires this.end != null;
	  @*/
	public /*@ pure @*/ Duration gameDuration() {
		return Duration.between(start, end);
	}
	
	
	@Override
	public /*@ pure @*/ void update() {
		view.drawOnScreen();
	}
	
	public static void main(String[] args) {
		View view = new CmdView();
		Controller controller = new Controller(view);
		controller.iniciarJogo();
		System.out.println(controller.moverCartas(1, 2, 3));
		System.out.println(controller.moverCartaTopo(1, 2));
		System.out.println(controller.isVencedor());
		controller.virarCartaFileira(3);
		controller.puxarCartaEstoque();
		controller.setPuxarTresCartasEstoque();
		controller.setPuxarUmaCartaEstoque();
		System.out.println(controller.getPilhas());
		controller.finalizar();
		System.out.println(controller.gameDuration());
		controller.update();
	}

}
