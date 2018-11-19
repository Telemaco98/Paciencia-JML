package model;

import java.util.ArrayList;

import util.Carta;

public class Estoque extends Pilha {

	public Estoque() {
		super();
	}
	
	public Estoque(ArrayList<Carta> cartasParaBaixo) {
		this();
		cartas.addAll(cartasParaBaixo);
	}
	
	@Override
	protected boolean verificarCarta(Carta carta) {
		return false;
	}

}
