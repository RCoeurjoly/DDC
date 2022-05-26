-- migrate:up
CREATE TABLE `arguments_when_returning` (
  `node_id` int unsigned,
  `name` char(255) NOT NULL DEFAULT '',
  `value` blob NOT NULL DEFAULT '',
  unique KEY (`node_id`, `name`),
  CONSTRAINT `arguments_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`id`),
  CONSTRAINT `arguments_when_returning_should_also_appear_on_entry` FOREIGN KEY (`node_id`, `name`) REFERENCES `arguments_on_entry` (`node_id`, `name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down
DROP TABLE arguments_when_returning;
