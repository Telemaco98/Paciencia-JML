package model;

import java.util.ArrayList;

import util.Carta;

public class Estoque extends Pilha {

	public Estoque() {
		super();
	}
	
	/*@ requires cartasParaBaixo != null;
	  @ assignable this.cartas;
	  @ ensures cartas.size(\old(this.cartas.size()) + cartasParaBaixo.size());
	  @ ensures cartas.constainsAll(\old(this.cartas));
	  @ ensures cartas.constainsAll(cartasParaBaixo);
	  @*/
	public Estoque(ArrayList<Carta> cartasParaBaixo) {
		this();
		cartas.addAll(cartasParaBaixo);
	}
	
	@Override
	protected /*@ pure @*/ boolean verificarCarta(Carta carta) {
		return false;
	}

}
