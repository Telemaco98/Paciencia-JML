package model;

import java.util.ArrayList;
import util.Carta;

public class Estoque extends Pilha {

	public Estoque() {
		super();
	}
	
	/*@ requires cartasParaBaixo != null;
	  @ assignable this.cartas;
	  @ ensures this.cartas.equals(\old(this.cartas).addAll(cartasParaBaixo));
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
