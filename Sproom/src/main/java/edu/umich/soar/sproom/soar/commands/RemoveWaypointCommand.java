/**
 * 
 */
package edu.umich.soar.sproom.soar.commands;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

import edu.umich.soar.sproom.Adaptable;
import edu.umich.soar.sproom.command.Waypoints;

import sml.Identifier;

/**
 * @author voigtjr
 *
 * Remove waypoint from waypoint system.
 */
public class RemoveWaypointCommand extends OutputLinkCommand {
	private static final Log logger = LogFactory.getLog(RemoveWaypointCommand.class);
	static final String NAME = "remove-waypoint";

	private static final String ID = "id";

	private final Identifier wme;
	private String id;

	public RemoveWaypointCommand(Identifier wme) {
		super(wme);
		this.wme = wme;
	}

	@Override
	protected OutputLinkCommand accept() {
		String id = wme.GetParameterValue(ID);
		if (id == null) {
			return new InvalidCommand(wme, "No " + ID);
		}
		
		logger.debug(id);
		addStatus(CommandStatus.ACCEPTED);
		return this;
	}
	
	@Override
	public void update(Adaptable app) {
		Waypoints waypoints = (Waypoints)app.getAdapter(Waypoints.class);
		waypoints.removeWaypoint(id);
		addStatus(CommandStatus.COMPLETE);
	}

}