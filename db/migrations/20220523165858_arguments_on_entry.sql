-- migrate:up
CREATE TABLE `arguments_on_entry` (
  `node_id` int unsigned,
  `argument_name` char(255) NOT NULL DEFAULT '',
  `argument_value` blob NOT NULL DEFAULT '',
  unique KEY (`node_id`, `argument_name`),
  CONSTRAINT `arguments_on_entry_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;

-- migrate:down
DROP TABLE arguments_on_entry;
